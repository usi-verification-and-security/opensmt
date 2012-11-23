/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef OPENSMT_CONTEXT_H
#define OPENSMT_CONTEXT_H

#include "Egraph.h"
#include "SimpSMTSolver.h"
#include "Tseitin.h"
#include "ANode.h"

class OpenSMTContext
{
public:
  //
  // For scripts
  //
  OpenSMTContext( int    argc
                , char * argv[ ] )
    : config_p     ( new SMTConfig( argc, argv ) )
    , config       ( *config_p )
    , sstore_p     ( new SStore( config ) )
    , sstore       ( *sstore_p )
    , egraph_p     ( new Egraph( config, sstore ) )
    , egraph       ( *egraph_p )
    , solver_p     ( new SimpSMTSolver( egraph, config ) )
    , solver       ( *solver_p )
    , cnfizer_p    ( new Tseitin( egraph, solver, config, sstore ) )
    , cnfizer      ( *cnfizer_p )
    , state        ( l_Undef )
    , nof_checksat ( 0 )
    , counter      ( 0 )
    , init         ( false )
  { }
  //
  // For API library
  //
  OpenSMTContext( )
    : config_p     ( new SMTConfig( ) )
    , config       ( *config_p )
    , sstore_p     ( new SStore( config ) )
    , sstore       ( *sstore_p )
    , egraph_p     ( new Egraph( config, sstore ) )
    , egraph       ( *egraph_p )
    , solver_p     ( new SimpSMTSolver( egraph, config ) )
    , solver       ( *solver_p )
    , cnfizer_p    ( new Tseitin( egraph, solver, config, sstore ) )
    , cnfizer      ( *cnfizer_p )
    , state        ( l_Undef )
    , nof_checksat ( 0 )
    , counter      ( 0 )
    , init         ( false )
  { 
    config.incremental = 1;
  }

  ~OpenSMTContext( )
  {
    assert( config_p );
    assert( sstore_p ); 
    assert( egraph_p );
    assert( solver_p );
    assert( cnfizer_p );
    delete cnfizer_p;
    delete solver_p;
    delete egraph_p;
    delete sstore_p;
    delete config_p;
  }

  //
  // Execute recorded commands
  //
  int           executeCommands      ( );

  //======================================================================
  //
  // Communication API
  //
  void          SetLogic             ( logic_t );                           // Set logic
  void          SetLogic             ( const char * );                      // Set logic
  void          SetOption            ( const char * );                      // Set option
  void          SetOption            ( const char *, const char * );        // Set option
  void          SetInfo              ( const Anode* );                      // Set info
  void          DeclareSort          ( const char *, int );                 // Declares a new sort
  void          DeclareFun           ( const char *, Snode *, Snode * );    // Declares a new function symbol

  void          Push                 ( );
  void          Pop                  ( );
  void          Reset                ( );
#ifndef SMTCOMP
  inline void   PrintModel           ( ostream & os ) { solver.printModel( os ); egraph.printModel( os ); }
#endif
  void          PrintConfig          ( ostream & os ) { config.printConfig(os); }

  void          GetProof             ( );
  void          GetInterpolants      ( );

  void          Assert               ( Enode * );               // Pushes assertion 
  lbool         CheckSAT             ( );                       // Command for (check-sat)
  void          Exit                 ( );                       // Command for (exit)

  //
  // Misc
  //
  void          PrintResult          ( const lbool &
                                     , const lbool & = l_Undef );
  void          DumpAssertionsToFile ( const char * file ) { egraph.dumpAssertionsToFile( file ); }

#ifdef PRODUCE_PROOF
  // Create interpolants with each A consisting of the specified partitions
  void          GetInterpolants(const vector<vector<int> >& partitions,
                                vector<Enode*>& interpolants);
#endif

  // 
  // For script: add a command to the queue
  //
  void          addAssert            ( Enode * );               // Command for (assert ...)
  void          addCheckSAT          ( );                       // Command for (check-sat)
  void          addPush              ( int );                   // Command for (push ...)
  void          addPop               ( int );                   // Command for (pop ...)
  void          addGetProof          ( );                       // Command for (get-proof)
  void          addGetInterpolants   ( );                       // Command for (get-interpolants)
  void          addExit              ( );                       // Command for (exit)
  //
  // API compatible with PB/CT
  //
  lbool   CheckSAT   ( vec< Enode * > & );                      // Command for (check-sat)
  lbool   CheckSAT   ( vec< Enode * > &, unsigned );            // Command for (check-sat)

  //======================================================================
  //
  // Term Creation API
  //
  //
  // Core functions
  //
  inline Enode * mkTrue      ( )                 { return egraph.mkTrue( ); }       
  inline Enode * mkFalse     ( )                 { return egraph.mkFalse( ); }       
  inline Enode * mkAnd       ( Enode * e )       { assert( e ); return egraph.mkAnd     ( e ); }
  inline Enode * mkOr        ( Enode * e )       { assert( e ); return egraph.mkOr      ( e ); }
  inline Enode * mkNot       ( Enode * e )       { assert( e ); return egraph.mkNot     ( e ); }
  inline Enode * mkImplies   ( Enode * e )       { assert( e ); return egraph.mkImplies ( e ); }
  inline Enode * mkXor       ( Enode * e )       { assert( e ); return egraph.mkXor     ( e ); }
  inline Enode * mkEq        ( Enode * e )       { assert( e ); return egraph.mkEq      ( e ); }
  inline Enode * mkIte       ( Enode * e )       { assert( e ); return egraph.mkIte     ( e ); }
  inline Enode * mkDistinct  ( Enode * e )       { assert( e ); return egraph.mkDistinct( e ); }
  //
  // Arithmetic functions
  //
  inline Enode * mkPlus      ( Enode * e )       { assert( e ); return egraph.mkPlus  ( e ); }
  inline Enode * mkMinus     ( Enode * e )       { assert( e ); return egraph.mkMinus ( e ); }
  inline Enode * mkTimes     ( Enode * e )       { assert( e ); return egraph.mkTimes ( e ); }
  inline Enode * mkUminus    ( Enode * e )       { assert( e ); return egraph.mkUminus( e ); }
  inline Enode * mkDiv       ( Enode * e )       { assert( e ); return egraph.mkDiv   ( e ); }
  inline Enode * mkLeq       ( Enode * e )       { assert( e ); return egraph.mkLeq   ( e ); }
  inline Enode * mkLt        ( Enode * e )       { assert( e ); return egraph.mkLt    ( e ); }
  inline Enode * mkGeq       ( Enode * e )       { assert( e ); return egraph.mkGeq   ( e ); }
  inline Enode * mkGt        ( Enode * e )       { assert( e ); return egraph.mkGt    ( e ); }

  inline Enode * mkCostBound ( Enode * e )       { assert( e ); return egraph.mkCostBound( e ); }
  inline Enode * mkCostIncur ( Enode * e )       { assert( e ); return egraph.mkCostIncur( e ); }
                                             
  inline Enode * mkCons   ( Enode * car
                          , Enode * cdr = NULL )        
  { 
    assert( car ); 
    return cdr == NULL ? egraph.cons( car ) : egraph.cons( car, cdr ); 
  }

  inline Enode * mkCons   ( list< Enode * > & l )            { return egraph.cons( l ); }

  inline Snode * mkCons   ( Snode * car
                          , Snode * cdr = NULL )        
  { 
    assert( car ); 
    return cdr == NULL ? sstore.cons( car ) : sstore.cons( car, cdr ); 
  }

  inline Snode * mkCons   ( list< Snode * > & l )            { return sstore.cons( l ); }

  inline void    mkBind   ( const char * v, Enode * t )      { assert( v ); assert( t ); egraph.mkDefine( v, t ); }
                                                        
  inline Enode * mkVar    ( const char * n, bool m = false ) { assert( n ); return egraph.mkVar( n, m ); }
  inline Enode * mkStore  ( Enode * a, Enode * i, Enode * e ) { assert( a && i && e ); return egraph.mkStore( a, i, e ); }
  inline Enode * mkSelect ( Enode * a, Enode * i )            { assert( a && i ); return egraph.mkSelect( a, i ); }
  inline Enode * mkDiff   ( Enode * a, Enode * b )           { assert( a && b ); return egraph.mkDiff( a, b ); }
  inline Enode * mkFun    ( const char * n, Enode * a )      { assert( n ); return egraph.mkFun( n, a ); }
  inline Enode * mkNum    ( const char * n )                 { assert( n ); return egraph.mkNum( n ); }
  inline Enode * mkNum    ( const Real & r )                 { return egraph.mkNum( r ); }

  //======================================================================
  //
  // Sort Creation API
  //
  
  inline Snode * mkSortBool  ( )           { return sstore.mkBool  ( ); }
  inline Snode * mkSortInt   ( )           { return sstore.mkInt   ( ); }
  inline Snode * mkSortReal  ( )           { return sstore.mkReal  ( ); }
  inline Snode * mkSortCost  ( )           { return sstore.mkCost  ( ); }

  inline Snode * mkSort      ( Snode * a )      { return sstore.mkDot( a ); }
//  inline Snode * mkSortVar   ( const char * n ) { return sstore.mkVar( n ); }
  inline Snode * mkSortVar   ( IdNode * n ) { return sstore.mkVar( n ); }

  //======================================================================
  //
  // Getty functions
  //
  inline SMTConfig & getConfig    ( )           { return config; }
  inline unsigned    getLearnts   ( )           { return solver.nLearnts( ); }
  inline unsigned    getDecisions ( )           { return solver.decisions; }
  inline lbool       getStatus    ( )           { return state; }
#ifndef SMTCOMP
  inline lbool       getModel     ( Enode * a ) { return solver.getModel( a ); } 
#endif

  //======================================================================
  //
  // Setty functions
  //
  inline void       setPolarityMode ( unsigned m ) { assert( m <= 6 ); config.sat_polarity_mode = m; }

private:

  SMTConfig *        config_p;                                   // Pointer to config
  SMTConfig &        config;                                     // Reference to config
  SStore *           sstore_p;                                   // Pointer to SStore
  SStore &           sstore;                                     // Reference to SStore
  Egraph *           egraph_p;                                   // Pointer to egraph
  Egraph &           egraph;                                     // Reference to egraph
  SimpSMTSolver *    solver_p;                                   // Pointer to solver
  SimpSMTSolver &    solver;                                     // Reference to solver
  Tseitin *          cnfizer_p;                                  // Pointer to cnfizer
  Tseitin &          cnfizer;                                    // Reference to cnfizer
                                                                 
  typedef enum                                                   
  {                                                              
      CMD_UNDEF                                                  // undefined command
    , SET_LOGIC                                                  // (set-logic)
    , SET_OPTION                                                 // (set-option)  
    , SET_INFO                                                   // (set-info)
    , DECLARE_SORT                                               // (declare-sort)
    , DEFINE_SORT                                                // (define-sort)
    , DECLARE_FUN                                                // (declare-fun)
    , DEFINE_FUN                                                 // (define-fun)
    , PUSH                                                       // (push)
    , POP                                                        // (pop)
    , ASSERT                                                     // (assert)
    , CHECK_SAT                                                  // (check-sat)
    , GET_ASSERTIONS                                             // (get-assertions)
    , GET_PROOF                                                  // (get-proof)
    , GET_INTERPOLANTS                                           // (get-interpolants)
    , GET_UNSAT_CORE                                             // (get-unsat-core)
    , GET_VALUE                                                  // (get-value)
    , GET_ASSIGNMENT                                             // (get-assignment)
    , GET_OPTION                                                 // (get-option)
    , GET_INFO                                                   // (get-info)
    , EXIT                                                       // (exit)
  } command_name_t;                                                   

  struct Command
  {
    Command( )
     : command( CMD_UNDEF )
     , enode    ( NULL )
     , sort_arg ( NULL )
     , sort_ret ( NULL )
    { }

    command_name_t command;
    Enode *        enode;
    Snode *        sort_arg;
    Snode *        sort_ret;
    char           str[256];
    int            num;
  };

  int     executeIncremental   ( );                                // Execute with incremental ability
  int     executeStatic        ( );                                // Execute without incremental ability (faster as more preproc is done)
  void    staticCheckSAT       ( );                                // For when only one check is required
#ifdef PRODUCE_PROOF
  void    staticCheckSATInterp ( );                                // For when only one check is required
#endif
  void    loadCustomSettings   ( );                                // Loads custom settings for SMTCOMP
                                                                 
  lbool              state;                                      // Current state of the solver
  vector< Command >  command_list;                               // Store commands to execute
  unsigned           nof_checksat;                               // Counter for CheckSAT commands
  unsigned           counter;                                    // Counter for creating new terms
  bool               init;                                       // Initialize
  bool               model_computed;
};

#endif
