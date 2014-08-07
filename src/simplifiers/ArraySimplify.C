/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>
      , Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include "ArraySimplify.h"
#include "Egraph.h"
#include "Global.h"

//#define ASVERB
//#define ARR_VERB

Enode *
ArraySimplify::doit( Enode * formula )
{
	assert( formula );
	vector< Enode * > unprocessed_enodes;
	egraph.initDup1( );

	//set<Enode*>indexWorld;

	unprocessed_enodes.push_back( formula );
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		Enode * enode = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( egraph.isDup1( enode ) )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
		Enode * arg_list;
		for ( arg_list = enode->getCdr( ) ;
				arg_list != egraph.enil ;
				arg_list = arg_list->getCdr( ) )
		{
			Enode * arg = arg_list->getCar( );

			assert( arg->isTerm( ) );
			//
			// Push only if it is unprocessed
			//
			if ( !egraph.isDup1( arg ) )
			{
				unprocessed_enodes.push_back( arg );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children )
			continue;

		// If the term is a select or store, update its array argument info adding a new array user
		if ( enode->isTerm( ) && enode->isStore( ) )
		{
			// Generate additional R(W(a,i,e),i)=e clause applying idx
			preprocIdx( enode );

			// Enode * a = enode->get1st( );
			// egraph.addStoreSuperterm(a,enode);
			//NB Not now but runtime!
			//egraph.addArrayRelevantIndex(enode,i);
		}
		if( enode->isTerm( ) && enode->isSelect( ) )
		{
			// Enode * a = enode->get1st();
			// Enode * i = enode->get2nd();
		}

//		if(enode->isTerm() && enode->isDTypeArrayIndex())
//			indexWorld.insert(enode);

		unprocessed_enodes.pop_back( );
		assert( !egraph.isDup1( enode ) );
		egraph.storeDup1( enode );
	}

	egraph.doneDup1( );

	// Generate additional clauses applying arrow up
	// preprocArrowUp( );

#ifdef ASVERB
	list<Enode*>::iterator it;
	for(it=new_clauses.begin();it!=new_clauses.end();it++)
		egraph.printStoreSupertermsList((*it)->get2nd()->get1st());
#endif

	new_clauses.push_back( formula );
	Enode * total = egraph.mkAnd( egraph.cons( new_clauses ) );

	//cout << "Index world size: " << indexWorld.size() << endl;

	return total;
}

// 
// Don't like to have to treat these cases without 
// using the already existent axiom procedures...
//
void ArraySimplify::preprocIdx( Enode * store )
{
	// create term R(W(a,i,e),i)=e
	Enode * i = store->get2nd( );
	Enode * e = store->get3rd( );

	// add clause R(W(a,i,e),i)=e
	Enode * newSelect = egraph.mkSelect( store, i );
	Enode * cl = egraph.mkEq( egraph.cons( newSelect, egraph.cons( e ) ) );
	new_clauses.push_back( cl );

#ifdef ARR_VERB
	cout << endl << "WAxiom:" << endl << store << endl << "->" << endl << cl << endl;
#endif
}

/*void ArraySimplify::preprocArrowUp( )
{
  // scan all select and store users of each array term a: R(a,j) and W(a,i,e)
  // for each pair st i!=j create a new R(W(a,i,e),j) (i=j already dealt in Idx)
  list< Enode * > aSelUsers, aStoUsers;
  list< Enode * >::iterator aSelUsersIt, aStoUsersIt;
  Enode *select, *store, *i ,*j, *e, *newSelect;
  Enode *lit1, *lit2, *lit3, *lit4, *cl1, *cl2;

  for( map< enodeid_t, usersData >::iterator arrayUsersIt = arrayUsers.begin( )
     ; arrayUsersIt != arrayUsers.end( )
     ; arrayUsersIt++ )
  {
    aSelUsers = arrayUsersIt->second.selectUsers;
    aStoUsers = arrayUsersIt->second.storeUsers;

    for ( aSelUsersIt = aSelUsers.begin( )
	; aSelUsersIt != aSelUsers.end( ) 
	; aSelUsersIt++)
    {
      for ( aStoUsersIt = aStoUsers.begin( )
	  ; aStoUsersIt != aStoUsers.end( ) 
	  ; aStoUsersIt++ )
      {
	select =* aSelUsersIt; 
	store =* aStoUsersIt;

	// create new term R(W(a,i,e),j)
	i = store->get2nd( );
	e = store->get3rd( );
	j = select->get2nd( );

	// case i==j indirectly treated in idx
	if( i != j )
	{
	  newSelect = egraph.mkSelect( store, j );

	  // add clause IF i!=j THEN R(W(a,i,e),j)=R(a,j)
	  // that is (i=j OR R(W(a,i,e),j)=R(a,j))
	  lit1 = egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) );
	  lit2 = egraph.mkEq( egraph.cons( newSelect, egraph.cons( select ) ) );
	  cl1 = egraph.mkOr( egraph.cons( lit1, egraph.cons( lit2 ) ) );

	  // add clause IF i=j THEN R(W(a,i,e),j)=e
	  // that is (NOT(i=j) OR R(W(a,i,e),j)=e)
	  lit3 = egraph.mkNot( egraph.cons( egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) ) ) );
	  lit4 = egraph.mkEq( egraph.cons( newSelect, egraph.cons( e ) ) );
	  cl2 = egraph.mkOr( egraph.cons( lit3, egraph.cons( lit4 ) ) );

	  new_clauses.push_back( cl1 );
	  new_clauses.push_back( cl2 );
#if VERBOSE
	  cerr << "Adding: " << cl1 << endl;
	  cerr << "Adding: " << cl2 << endl;
#endif
	}
      }
    }
  }
}

// R(W(b,i,e),i)=e
// RB: REMOVE ?
Enode * ArraySimplify::simp1( Enode * enode, bool & appl )
{
  assert( false );
  Enode * a = egraph.valDupMap1( enode->get1st( ) ); 
  assert( a );
  Enode * i = egraph.valDupMap1( enode->get2nd( ) ); 
  assert( i );

  if ( a->isTerm( ) && a->isStore( ) )
  {
    Enode * indexStore = egraph.valDupMap1( a->get2nd() ); 
    assert( indexStore );
    Enode * elementStore = egraph.valDupMap1( a->get3rd() ); 
    assert( elementStore );

    // Substitution by application axiom R(W(b,i,e),i)=e
    if ( i == indexStore )
    {
      Enode * result = elementStore;
      appl = true;
      return result;
    }
  }
  return enode;
}

// W(W(b,i,f),i,e)=W(b,i,e)
// RB: REMOVE ?
Enode * ArraySimplify::simp2( Enode * enode, bool & appl )
{
  assert( false );
  Enode * a = egraph.valDupMap1( enode->get1st( ) ); 
  assert( a );
  Enode * i = egraph.valDupMap1( enode->get2nd( ) ); 
  assert( i );
  Enode * e = egraph.valDupMap1( enode->get3rd( ) ); 
  assert( e );

  if ( a->isTerm( ) && a->isStore( ) )
  {
    Enode * b = egraph.valDupMap1( a->get1st() ); 
    assert( b );
    Enode * indexStore = egraph.valDupMap1( a->get2nd() ); 
    assert( indexStore );

    // Substitution by application axiom W(W(b,i,f),i,e)=W(b,i,e)
    if ( i == indexStore )
    {
      Enode * result = egraph.mkStore(b,i,e);
      appl = true;
      return result;
    }
  }
  return enode;
}

// W(a,i,R(a,i))=a
// RB: REMOVE ?
Enode * ArraySimplify::simp3( Enode * enode, bool & appl )
{
  assert( false );
  Enode * a = egraph.valDupMap1( enode->get1st( ) ); 
  assert( a );
  Enode * i = egraph.valDupMap1( enode->get2nd( ) ); 
  assert( i );
  Enode * e = egraph.valDupMap1( enode->get3rd( ) ); 
  assert( e );

  if ( e->isTerm( ) && e->isSelect( ) )
  {
    Enode * indexSelect = egraph.valDupMap1( e->get2nd( ) ); 
    assert( indexSelect );
    Enode * arraySelect = egraph.valDupMap1( e->get1st() ); 
    assert( arraySelect );

    // Substitution by application axiom W(a,i,R(a,i))=a
    if ( i == indexSelect && a == arraySelect )
    {
      Enode * result = a;
      appl = true;
      return result;
    }
  }
  return enode;
}*/

