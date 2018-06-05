/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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

#ifndef API_INTERPRET_H
#define API_INTERPRET_H

#include "smt2newcontext.h"
#include "SStore.h"
#include "PtStructs.h"

// forward declarations
class Logic;
class SMTConfig;
class Theory;
class SimpSMTSolver;
class MainSolver;
class THandler;

class LetFrame {
  private:
    static uint32_t id_cnt;
    uint32_t id_;
    Map<const char*, PTRef, StringHash, Equal<const char*> > frameMap;
//    VecMap<const char*, PTRef, StringHash, Equal<const char*> > frameMap;
  public:
    LetFrame() : id_(id_cnt++) {}
    bool        contains(const char* s) const { return frameMap.has(s); }
//    void        insert  (const char* key, const vec<PTRef>& value) { frameMap.insert(key, value); }
    void        insert  (const char* key, PTRef value) { frameMap.insert(key, value); }
    uint32_t    getId   () const { return id_; }
    PTRef       operator[] (const char* s) { return frameMap[s]; }
    PTRef       operator[] (const char* s) const { return frameMap[s]; }
//    vec<PTRef>&  operator[] (const char* s) { return frameMap[s]; }
//    const vec<PTRef>& operator[] (const char* s) const { return frameMap[s]; }
};


class Interpret {
  protected:
    SMTConfig      &config;
    Theory         *theory;
    THandler       *thandler;
    Logic          *logic;
    SimpSMTSolver  *solver;

    bool                        f_exit;

    IdRef                       newIdentifier(ASTNode& n);
    char*                       buildSortName(ASTNode& n);
    SRef                        newSort      (ASTNode& n);

    void                        setInfo(ASTNode& n);
    void                        getInfo(ASTNode& n);
    void                        setOption(ASTNode& n);
    void                        getOption(ASTNode& n);
    void                        writeState(const char* fname);
    void                        writeSplits(const char* fname);
    void                        writeSplits_smtlib2(const char* fname);
    bool                        declareFun(ASTNode& n); //(const char* fname, const vec<SRef>& args);
    bool                        declareConst(ASTNode& n); //(const char* fname, const SRef ret_sort);
    bool                        defineFun(const ASTNode& n);
    bool                        checkSat();
    void                        getValue(const list<ASTNode*>* term);
    bool                        push();
    bool                        pop();
    PTRef                       parseTerm(const ASTNode& term, vec<LetFrame>& let_branch);
    void                        exit();
#ifdef PRODUCE_PROOF
    void                        GetProof();
    void                        getInterpolants(const ASTNode& n);
#endif
    void                        interp (ASTNode& n);
    void                        execute(const ASTNode* n);

    void                        notify_formatted(bool error, const char* s, ...);
    void                        notify_success();
    void                        comment_formatted(const char* s, ...) const;
    bool                        addLetName(const char* s, const PTRef args, LetFrame& frame);
    PTRef                       letNameResolve(const char* s, const vec<LetFrame>& frame) const;
    PTRef                       insertTerm(const char* s, const vec<PTRef>& args);
    int                         asrt_lev;

    int                         sat_calls; // number of sat calls

    // Named terms for getting variable values
    Map<const char*,PTRef,StringHash,Equal<const char*> > nameToTerm;
    VecMap<PTRef,const char*,PTRefHash,Equal<PTRef> > termToNames;
    vec<const char*>            term_names;

    vec<SRef>                   vec_sr_empty; // For faster comparison with empty vec
    vec<PTRef>                  vec_ptr_empty;

    vec<PTRef> assertions;

    virtual void new_solver();

  public:
    Interpret(SMTConfig& c)
        : logic   (NULL)
        , theory(NULL)
        , thandler(NULL)
        , solver(NULL)
        , main_solver(NULL)
        , f_exit(false)
        , asrt_lev(0)
        , sat_calls(0)
        , config(c)
        , parse_only(false) { }

    Interpret(SMTConfig& c, Logic *_l, Theory *_t, THandler *_th, SimpSMTSolver *_s, MainSolver *_m)
        : logic   (_l)
        , theory(_t)
        , thandler(_th)
        , solver(_s)
        , main_solver(_m)
        , f_exit(false)
        , asrt_lev(0)
        , sat_calls(0)
        , config(c)
        , parse_only(false) { }

    ~Interpret();

    int interpFile(FILE* in);
    int interpFile(char *content);
    int interpInteractive(FILE* in);
    int interpPipe();

    ValPair getValue       (PTRef tr) const;
    bool    getAssignment  ();

    MainSolver   *main_solver;

    bool parse_only;
    PTRef getParsedFormula();
    vec<PTRef>& getAssertions() { return assertions; }
};

#endif
