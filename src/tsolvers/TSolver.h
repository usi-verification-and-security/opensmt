/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

#ifndef TSOLVER_H
#define TSOLVER_H

#include "Enode.h"
#include "SMTConfig.h"
#include "SolverTypes.h"

class SimpSMTSolver;
class Egraph;
class SStore;

#ifdef STATISTICS
struct TSolverStats
{
  TSolverStats ( )
    : sat_calls         ( 0 )
    , uns_calls         ( 0 )
    , conflicts_sent    ( 0 )
    , avg_conf_size     ( 0 )
    , max_conf_size     ( 0 )
    , min_conf_size     ( 32767 )
    , deductions_done   ( 0 )
    , deductions_sent   ( 0 )
    , reasons_sent      ( 0 )
    , avg_reas_size     ( 0 )
    , max_reas_size     ( 0 )
    , min_reas_size     ( 32767 )
    , sod_done          ( 0 )
    , sod_sent          ( 0 )
    , avg_sod_size      ( 0 )
    , max_sod_size      ( 0 )
    , min_sod_size      ( 32767 )
  { }

  // Statistics for theory solvers
  void printStatistics ( ostream & os )
  {
    os << "; Satisfiable calls........: " << sat_calls << endl;
    os << "; Unsatisfiable calls......: " << uns_calls << endl;
    if ( uns_calls > 0 )
    {
      os << "; Conflicts sent...........: " << conflicts_sent << endl;
      if ( conflicts_sent > 0 )
      {
        os << "; Average conflict size....: " << avg_conf_size / (float)conflicts_sent << endl;
        os << "; Max conflict size........: " << max_conf_size << endl;
        os << "; Min conflict size........: " << min_conf_size << endl;
      }
    }
    if ( sat_calls > 0 )
    {
      os << "; Deductions done..........: " << deductions_done << endl;
      os << "; Deductions sent..........: " << deductions_sent << endl;
      os << "; Reasons sent.............: " << reasons_sent << endl;
      if ( reasons_sent > 0 )
      {
	os << "; Average reason size......: " << avg_reas_size / (float)reasons_sent << endl;
	os << "; Max reason size..........: " << max_reas_size << endl;
	os << "; Min reason size..........: " << min_reas_size << endl;
      }
      os << "; SOD done.................: " << sod_done << endl;
      os << "; SOD sent.................: " << sod_sent << endl;
      if ( sod_sent > 0 )
      {
	os << "; Average reason size......: " << avg_reas_size / (float)sod_sent << endl;
	os << "; Max reason size..........: " << max_reas_size << endl;
	os << "; Min reason size..........: " << min_reas_size << endl;
      }
    }
  }

  // Calls statistics
  long  sat_calls;
  long  uns_calls;
  // Conflict statistics
  int   conflicts_sent;
  float avg_conf_size;
  int   max_conf_size;
  int   min_conf_size;
  // Deductions statistics
  int   deductions_done;
  int   deductions_sent;
  int   reasons_sent;
  float avg_reas_size;
  int   max_reas_size;
  int   min_reas_size;
  // Deductions statistics
  int   sod_done;
  int   sod_sent;
  float avg_sod_size;
  int   max_sod_size;
  int   min_sod_size;
};
#endif

class TSolver
{
public:

  TSolver ( const int i, const char * n, SMTConfig & c )
    : id     ( i )
    , name   ( n )
    , config ( c )
  { }

  virtual ~TSolver ( ) { }

  virtual lbool               inform              ( PTRef )               = 0;  // Inform the solver about the existence of a theory atom
  virtual bool                assertLit           ( PTRef, bool = false ) = 0;  // Assert a theory literal
  virtual void                pushBacktrackPoint  ( )                       = 0;  // Push a backtrack point
  virtual void                popBacktrackPoint   ( )                       = 0;  // Backtrack to last saved point
  virtual bool                check               ( bool )                  = 0;  // Check satisfiability
  inline const string &       getName             ( ) { return name; }            // The name of the solver
  virtual lbool               evaluate            ( PTRef ) { return l_Undef; } // Evaluate the expression in the current state
#ifdef PRODUCE_PROOF
  virtual Enode *             getInterpolants     ( logic_t & ) { return interpolants; }
#endif

protected:

  const int                   id;               // Id of the solver
  const string                name;             // Name of the solver
  SMTConfig &                 config;           // Reference to configuration
  vec< size_t >               backtrack_points; // Keeps track of backtrack points
#ifdef PRODUCE_PROOF
  Enode *                     interpolants;     // Store interpolants
#endif
};

class OrdinaryTSolver : public TSolver
{
public:

  OrdinaryTSolver ( const int           i
                  , const char *        n
		  , SMTConfig &         c
		  , Egraph &            e
		  , SStore &            t
		  , vector< Enode * > & x
		  , vector< Enode * > & d
		  , vector< Enode * > & s )
    : TSolver     ( i, n, c )
    , egraph      ( e )
    , sstore      ( t )
    , explanation ( x )
    , deductions  ( d )
    , suggestions ( s )
  { }

  virtual ~OrdinaryTSolver ( )
  { }

  virtual bool belongsToT   ( Enode * ) = 0; // Atom belongs to this theory
  virtual void computeModel ( )         = 0; // Compute model for variables

protected:

  Egraph &            egraph;      // Reference to egraph
  SStore &            sstore;      // Reference to sstore
  vector< Enode * > & explanation; // Stores the explanation
  vector< Enode * > & deductions;  // List of deductions
  vector< Enode * > & suggestions; // List of suggestions for decisions
};

class CoreTSolver : public TSolver
{
public:

  CoreTSolver ( const int    i
              , const char * n
	      , SMTConfig &  c )
    : TSolver         ( i, n, c )
    , deductions_next ( 0 )
    , solver          ( NULL )
  { }

  virtual ~CoreTSolver ( )
  { }

//  virtual vec< PTRef > &      getConflict    ( bool = false ) = 0; // Return conflict
  virtual void                getConflict    ( bool, vec<PtAsgn>& ) = 0; // Return conflict
  virtual PtAsgn_reason&      getDeduction   ( )              = 0; // Return an implied node based on the current state
  inline void                 setSolver      ( SimpSMTSolver * s ) { assert( s ); assert( solver == NULL || solver == s); solver = s; }
  virtual void                splitOnDemand  ( vec< PTRef > &
                                             , const int )    = 0; // For splitting on demand

protected:

  vec< OrdinaryTSolver * >    tsolvers;            // List of ordinary theory solvers

public:
#ifdef STATISTICS
  TSolverStats                tsolver_stats;       // Statistical info for this solver
#endif

protected:
  vec< PTRef >                explanation;         // Stores the explanation
  vec< PtAsgn_reason >        deductions;          // List of deductions
  size_t                      deductions_next;     // Index of next deduction to communicate
  vec< size_t >               deductions_lim;      // Keeps track of deductions done up to a certain point
  vec< size_t >               deductions_last;     // Keeps track of deductions done up to a certain point
  vec< PTRef >                suggestions;         // List of suggestions for decisions
  SimpSMTSolver *             solver;              // Pointer to solver
};

#endif
