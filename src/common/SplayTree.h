/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

/*********************************************************************
The code here is adapted from simple top-down splay from the publicy
available code of D. Sleator, avaialable via anonymous ftp from
spade.pc.cs.cmu.edu in directory /usr/sleator/public.

I've made it a template class parametrizable with the data T to be
stored and the comparison function C
*********************************************************************/

#ifndef SPLAY_TREE_H
#define SPLAY_TREE_H

template <class T, class C >
class SplayTree
{
public:

  SplayTree( ) 
    : last_node  ( NULL )
    , initialized( false ) 
#ifndef SMTCOMP
    , size       ( 0 )
#endif
  { }

  ~SplayTree( ) 
  { 
    deleteTree( root ); 
    delete bnil_node;
    if ( last_node )
      delete last_node;
  }

  void setNil( T & e )
  {
    assert( !initialized );
    //
    // Initialize splay tree with just the
    // node containing an atom that we use
    // to express a failure in the search
    //
    bnil_node = new Bnode;
    bnil_node->left  = bnil_node;
    bnil_node->right = bnil_node;
    bnil_node->element = e;
    root = bnil_node;
    initialized = true;
  }

  T &         find    ( T & x );
  inline bool isEmpty ( ) const { assert( initialized ); return root == bnil_node; }

  T &  insert         ( T & );
  void remove         ( T & );
  //
  // Copy is not supported
  //
  const SplayTree & operator=( const SplayTree & rhs ) { assert( false ); }

#ifndef SMTCOMP
  void printStatistics( ostream & );
#endif

private:
  //
  // Nodes of the tree
  //
  struct Bnode
  {

    Bnode( ) 
      : left( NULL )
      , right( NULL ) 
    { }

    Bnode( T & t, Bnode * lt, Bnode * rt )
      : element( t )
      , left   ( lt )
      , right  ( rt ) 
    { }

    T       element;
    Bnode * left;
    Bnode * right;
  };
 
  void deleteTree           ( Bnode * t );
  void rotateWithLeftChild  ( Bnode * & k2 );
  void rotateWithRightChild ( Bnode * & k1 );
  void splay                ( T & x, Bnode * & t );

  Bnode *  root;             // rott of the tree
  Bnode *  last_node;        // rott of the tree
  Bnode *  bnil_node;        // nil node
  C        cmp;              // Comparison structure
  bool     initialized;      // Check if the nil node has been initialized
#ifndef SMTCOMP
  unsigned size;             // Keep track of the size of the tree (number of nodes)
#endif
};

//
// Inserts an element
//
template <class T, class C>
T & SplayTree< T, C >::insert( T & x )
{
  assert( initialized );

  if( last_node == NULL )
  {
    last_node = new Bnode;
#ifndef SMTCOMP
    size ++;
#endif
  }

  last_node->element = x;

  if( root == bnil_node )
  {
    last_node->left = last_node->right = bnil_node;
    root = last_node;
  }
  else
  {
    splay( x, root );
    // 
    // Element is less than
    //
    if( cmp( x, root->element ) )
    {
      last_node->left = root->left;
      last_node->right = root;
      root->left = bnil_node;
      root = last_node;
    }
    // 
    // Element is greater than
    //
    else if( cmp( root->element, x ) )
    {
      last_node->right = root->right;
      last_node->left = root;
      root->right = bnil_node;
      root = last_node;
    }
    //
    // Element is equal; do not insert
    //
    else
    {
      return root->element; 
    }
  }

  last_node = NULL;  // Element inserted
  return x;          // Insertion took place
}

//
// Remove element
//
template <class T, class C>
void SplayTree< T, C >::remove( T & x )
{
  assert( initialized );

  Bnode * new_tree;

  // If x is found, it will be at the root
  splay( x, root );
  if( root->element != x )
    return;   // Item not found; do nothing

  if( root->left == bnil_node )
    new_tree = root->right;
  else
  {
    // Find the maximum in the left subtree
    // Splay it to the root; and then attach right child
    new_tree = root->left;
    splay( x, new_tree );
    new_tree->right = root->right;
  }
  delete root;
  root = new_tree;
}

//
// Find an element
//
template <class T, class C>
T & SplayTree< T, C >::find( T & x )
{
  assert( initialized );

  if( isEmpty( ) ) 
    return bnil_node;
  splay( x, root );
  if( root->element != x )
    return bnil_node;

  return root->element;
}

//
// Splay the tree with respect to t
//
template <class T, class C>
void SplayTree< T, C >::splay( T & t, Bnode * & n )
{
  assert( initialized );

  Bnode *leftTreeMat, *rightTreeMin;
  static Bnode header;

  header.left = header.right = bnil_node;
  leftTreeMat = rightTreeMin = &header;

  bnil_node->element = t;   

  for(;;)
  {
    if( cmp( t, n->element ) )
    {
      if( cmp( t, n->left->element ) )
	rotateWithLeftChild( n );
      if( n->left == bnil_node )
	break;
      // Link Right
      rightTreeMin->left = n;
      rightTreeMin = n;
      n = n->left;
    }
    else if( cmp( n->element, t ) )
    {
      if( cmp( n->right->element, t ) )
	rotateWithRightChild( n );
      if( n->right == bnil_node )
	break;
      // Link Left
      leftTreeMat->right = n;
      leftTreeMat = n;
      n = n->right;
    }
    else
      break;
  }

  leftTreeMat->right = n->left;
  rightTreeMin->left = n->right;
  n->left = header.right;
  n->right = header.left;
}

//
// Rotate using left child of k2
//
template <class T, class C>
void SplayTree< T, C >::rotateWithLeftChild( Bnode * & k2 )
{
  assert( initialized );
  Bnode * k1 = k2->left;
  k2->left = k1->right;
  k1->right = k2;
  k2 = k1;
}

//
// Rotate using right child of k1
// 
template <class T, class C>
void SplayTree< T, C >::rotateWithRightChild( Bnode * & k1 )
{
  assert( initialized );
  Bnode * k2 = k1->right;
  k1->right = k2->left;
  k2->left = k1;
  k1 = k2;
}

//
// Recursively delete the tree
//
template <class T, class C>
void SplayTree< T, C >::deleteTree( Bnode * t )
{
  assert( initialized );
  if( t != t->left )
  {
    deleteTree( t->left );
    deleteTree( t->right );
    delete t;
  }
}

#ifndef SMTCOMP
template <class T, class C>
void SplayTree< T, C >::printStatistics( ostream & os )
{
  os << "#" << endl;
  os << "# Total bnodes..........: " << size << endl;
  os << "# Bnode size in memory..: " << size * sizeof( Bnode ) / ( 1024.0 * 1024.0 ) << " MB" << endl;
  os << "# Avg size per bnode....: " << sizeof( Bnode ) << " B" << endl;
}

#endif

#endif
