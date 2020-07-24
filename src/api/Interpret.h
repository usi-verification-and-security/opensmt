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
#include "SymRef.h"

// forward declarations
class Logic;
class Theory;
class SimpSMTSolver;
class MainSolver;
class THandler;

class LetFrame {
  private:
    static uint32_t id_cnt;
    uint32_t id_;
    Map<const char*, PTRef, StringHash, Equal<const char*> > *frameMap;
  public:
    LetFrame() : id_(id_cnt++), frameMap(new Map<const char*, PTRef, StringHash, Equal<const char*>>()) {}
    LetFrame(const Map<const char*, PTRef, StringHash, Equal<const char*>>& imap) : id_(id_cnt++), frameMap(new Map<const char*, PTRef, StringHash, Equal<const char*>>()) { imap.copyTo(*frameMap); }
    LetFrame(LetFrame&& o) : id_(o.id_) { frameMap = o.frameMap; o.frameMap = nullptr; }
    LetFrame(const LetFrame& o) : id_(o.id_)  { o.frameMap->copyTo(*frameMap); }
    ~LetFrame() { if (frameMap != nullptr) delete frameMap; }
    LetFrame& operator= (LetFrame&& o) { if (this != &o) { delete frameMap; frameMap = o.frameMap; o.frameMap = nullptr; } return *this; }
    bool        contains(const char* s) const { return frameMap->has(s); }
//    void        insert  (const char* key, const vec<PTRef>& value) { frameMap.insert(key, value); }
    void        insert  (const char* key, PTRef value) { frameMap->insert(key, value); }
    uint32_t    getId   () const { return id_; }
    PTRef       operator[] (const char* s) { return (*frameMap)[s]; }
    PTRef       operator[] (const char* s) const { return (*frameMap)[s]; }
//    vec<PTRef>&  operator[] (const char* s) { return frameMap[s]; }
//    const vec<PTRef>& operator[] (const char* s) const { return frameMap[s]; }
};


class Interpret {
  protected:
    SMTConfig      &config;
    Logic          *logic;
    Theory         *theory;
    THandler       *thandler;
    SimpSMTSolver  *solver;
    MainSolver     *main_solver;

    bool            f_exit;
    int             asrt_lev;
    int             sat_calls; // number of sat calls
    bool            parse_only;

    // Named terms for getting variable values
    Map<const char*,PTRef,StringHash,Equal<const char*>> nameToTerm;
    VecMap<PTRef,const char*,PTRefHash,Equal<PTRef> > termToNames;
    vec<char*>      term_names; // For (! <t> :named <n>) constructs.  if Itp is enabled, this maps a
                                            // partition to it name.
    vec<PTRef>      vec_ptr_empty;

    vec<PTRef>      assertions;
    vec<SymRef>     user_declarations;

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
    void                        getValue(const std::vector<ASTNode*>* term);
    void                        getModel();
    bool                        push();
    bool                        pop();
    PTRef                       parseTerm(const ASTNode& term, vec<LetFrame>& let_branch);
    void                        exit();
    void                        getInterpolants(const ASTNode& n);
    void                        interp (ASTNode& n);

    void                        notify_formatted(bool error, const char* s, ...);
    void                        notify_success();
    void                        comment_formatted(const char* s, ...) const;
    bool                        addLetName(const char* s, const PTRef args, LetFrame& frame);
    PTRef                       letNameResolve(const char* s, const vec<LetFrame>& frame) const;
    PTRef                       insertTerm(const char* s, const vec<PTRef>& args);



    virtual void new_solver();

  public:


    Interpret(SMTConfig& c, Logic *_l, Theory *_t, THandler *_th, SimpSMTSolver *_s, MainSolver *_m)
        : config     (c)
        , logic      (_l)
        , theory     (_t)
        , thandler   (_th)
        , solver     (_s)
        , main_solver(_m)
        , f_exit     (false)
        , asrt_lev   (0)
        , sat_calls  (0)
        , parse_only (false) { }

    Interpret(SMTConfig& c) : Interpret(c, nullptr, nullptr, nullptr, nullptr, nullptr) { }

    ~Interpret();

    int interpFile(FILE* in);
    int interpFile(char *content);
    int interpPipe();

    void    execute(const ASTNode* n);
    bool    gotExit() const { return f_exit; }


    ValPair getValue       (PTRef tr) const;
    bool    getAssignment  ();

    void    reportError(char const * msg) { notify_formatted(true, msg); }


    PTRef getParsedFormula();
    vec<PTRef>& getAssertions() { return assertions; }
    bool is_top_level_assertion(PTRef ref);
    int get_assertion_index(PTRef ref);
    void setParseOnly() { parse_only = true; }
};

#endif
