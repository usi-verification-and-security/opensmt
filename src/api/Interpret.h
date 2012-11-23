#include "parsers/smt2new/smt2newcontext.h"
#include "common/StringMap.h"
#include "Egraph.h"
#include "SimpSMTSolver.h"
#include "Tseitin.h"
#include "sorts/Sort.h"
#include "logics/Logic.h"
#include "terms/TStore.h"
#include "terms/Term.h"

enum ConfType { O_EMPTY, O_STR, O_SYM, O_NUM, O_DEC, O_HEX, O_BIN, O_LIST, O_ATTR, O_BOOL };

class ConfValue {
  public:
    ConfType type;
    union { char* strval; int numval; double decval; uint32_t unumval; list<ConfValue*>* configs; };
    ConfValue() : type(O_EMPTY) {};
    ConfValue(const ASTNode& s_expr_n);
    char* toString();
};

class Info {
  private:
    char*      name;
    ConfValue   value;
  public:
    Info(ASTNode& n);
    Info() : name(strdup("")) {};
    inline char* toString() { return value.toString(); };
};


class Option {
  private:
    char*       name;
    ConfValue   value;
  public:
    Option(ASTNode& n);
    Option() : name(strdup("")) {};
    inline char* toString() { return value.toString(); };
};

class LetFrame {
  private:
    static uint32_t id_cnt;
    uint32_t id_;
    VecMap<const char*, TRef, StringHash, Equal<const char*> > frameMap;
  public:
    LetFrame() : id_(id_cnt++) {}
    bool        contains(const char* s) const { return frameMap.contains(s); }
    void        insert  (const char* key, const vec<TRef>& value) { frameMap.insert(key, value); }
    uint32_t    getId   () const { return id_; }
    vec<TRef>&  operator[] (const char* s) { return frameMap[s]; }
    const vec<TRef>& operator[] (const char* s) const { return frameMap[s]; }
};


class Interpret {
  private:
    Map<char*,Info,StringHash,Equal<char*> >   infoTable;
    Map<char*,Option,StringHash,Equal<char*> > optionTable;
    SMTConfig                                  config;
    TStore                                     tstore;
    SStore                                     store;


    Logic                       logic;

    bool                        f_exit;

    void                        setInfo(ASTNode& n);
    void                        getInfo(ASTNode& n);
    void                        setOption(ASTNode& n);
    void                        getOption(ASTNode& n);
    bool                        declareFun(const char* fname, const vec<SRef>& args);
    SRef                        parseTerm(const ASTNode& term, vec<LetFrame>& let_branch);
    void                        exit();

    bool                        interp (ASTNode& n);
    void                        execute(const ASTNode* n);

    void                        notify_formatted(bool error, const char* s, ...);
    void                        notify_success();
    void                        comment_formatted(const char* s, ...) const;
    bool                        addLetName(const char* s, const TRef args, LetFrame& frame);
    TRef                        letNameResolve(const char* s, const vec<SRef>& args, const vec<LetFrame>& let_branch) const;
    int                         asrt_lev;

    vec<SRef>                   vec_empty; // For faster comparison with empty vec

  public:
    // Constructor initiates a default logic.  Not sure if this is the best way to go...
    Interpret() : store(config), logic(config, store, tstore), f_exit(false), asrt_lev(0) {};

    int                         interpFile(FILE* in);
    int                         interpInteractive(FILE* in);
};
