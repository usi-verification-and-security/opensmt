#include "parsers/smt2new/smt2newcontext.h"
#include "common/StringMap.h"
//#include "Egraph.h"
#include "SimpSMTSolver.h"
//#include "Tseitin.h"
#include "sorts/SStore.h"
#include "sorts/Sort.h"
#include "logics/Logic.h"
#include "terms/TStore.h"
#include "terms/Term.h"
#include "pterms/PtStore.h"
#include "Tseitin.h"
#include "egraph/Egraph.h"
#include "smtsolvers/SMTConfig.h"

class LetFrame {
  private:
    static uint32_t id_cnt;
    uint32_t id_;
    Map<const char*, PTRef, StringHash, Equal<const char*> > frameMap;
//    VecMap<const char*, PTRef, StringHash, Equal<const char*> > frameMap;
  public:
    LetFrame() : id_(id_cnt++) {}
    bool        contains(const char* s) const { return frameMap.contains(s); }
//    void        insert  (const char* key, const vec<PTRef>& value) { frameMap.insert(key, value); }
    void        insert  (const char* key, PTRef value) { frameMap.insert(key, value); }
    uint32_t    getId   () const { return id_; }
    PTRef       operator[] (const char* s) { return frameMap[s]; }
    PTRef       operator[] (const char* s) const { return frameMap[s]; }
//    vec<PTRef>&  operator[] (const char* s) { return frameMap[s]; }
//    const vec<PTRef>& operator[] (const char* s) const { return frameMap[s]; }
};


class Interpret {
  private:
    SMTConfig                                  config;
    SStore                                     store;    // Sorts
    TStore                                     tstore;   // Terms (more like symbols)
    PtStore                                    ptstore;  // Proper terms
    Logic                                      logic;
    Tseitin                                    ts;

    Map<const char*,PTRef,StringHash,Equal<const char*> > nameToTerm;
    VecMap<PTRef,const char*,PTRefHash,Equal<PTRef> > termToNames;
    vec<const char*>            term_names;

    bool                        f_exit;

    void                        setInfo(ASTNode& n);
    void                        getInfo(ASTNode& n);
    void                        setOption(ASTNode& n);
    void                        getOption(ASTNode& n);
    bool                        declareFun(const char* fname, const vec<SRef>& args);
    bool                        checkSat(const char*);
    bool                        getAssignment(const char*);
    PTRef                       parseTerm(const ASTNode& term, vec<LetFrame>& let_branch);
    void                        exit();

    bool                        interp (ASTNode& n);
    void                        execute(const ASTNode* n);

    void                        notify_formatted(bool error, const char* s, ...);
    void                        notify_success();
    void                        comment_formatted(const char* s, ...) const;
    bool                        addLetName(const char* s, const PTRef args, LetFrame& frame);
    PTRef                       letNameResolve(const char* s, const vec<LetFrame>& frame) const;
    PTRef                       insertTerm(const char* s, const vec<PTRef>& args);
    int                         asrt_lev;

    int                         sat_calls; // number of sat calls

    vec<SRef>                   vec_empty; // For faster comparison with empty vec

  public:
    // Constructor initiates a default logic.  Not sure if this is the best way to go...
    Interpret() :
          store(config)
        , ptstore(tstore, store)
        , logic(config, store, tstore, ptstore)
        , ts( ptstore
            , config
            , tstore
            , store
            , logic )
        , f_exit(false)
        , asrt_lev(0)
        , sat_calls(0) {};

    int                         interpFile(FILE* in);
    int                         interpInteractive(FILE* in);
};
