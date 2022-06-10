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
#include "Logic.h"
#include "MainSolver.h"
#include "ScopedVector.h"

#include <unordered_map>

class DefinedFunctions {
    std::unordered_map<std::string,TemplateFunction> defined_functions;
    opensmt::ScopedVector<std::string> scopedNames;

public:
    bool has(const std::string& name) const { return defined_functions.find(name) != defined_functions.end(); }

    void insert(const std::string& name, TemplateFunction && templ, bool scoped = false) {
        assert(not has(name));
        defined_functions[name] = std::move(templ);
        if (scoped) { scopedNames.push(name); }
    }

    TemplateFunction & operator[](const char* name) {
        assert(has(name));
        return defined_functions[name];
    }

    void pushScope() { scopedNames.pushScope(); }

    void popScope() {
        scopedNames.popScope([&](std::string const & name) {
            defined_functions.erase(name);
        });
    }
};

class LetBinder {
    PTRef currentValue;
    std::vector<PTRef>* shadowedValues;
public:
    LetBinder(PTRef val) : currentValue(val), shadowedValues(nullptr) {}
    ~LetBinder() { delete shadowedValues; }
    LetBinder(const LetBinder&) = delete;
    LetBinder& operator=(const LetBinder&) = delete;
    LetBinder(LetBinder&&) = default;
    LetBinder& operator=(LetBinder&&) = default;
    PTRef getValue() const { return currentValue; }
    bool hasShadowValue() const { return shadowedValues && !shadowedValues->empty(); }
    void restoreShadowedValue() { assert(hasShadowValue()); currentValue = shadowedValues->back(); shadowedValues->pop_back(); }
    void addValue(PTRef val) {
        if (not shadowedValues) {
            shadowedValues = new std::vector<PTRef>();
        }
        shadowedValues->push_back(currentValue);
        currentValue = val;
    }
};

class LetRecords {
    std::unordered_map<const char*, LetBinder, StringHash, Equal<const char*> > letBinders;
    std::vector<const char*> knownBinders;
    std::vector<std::size_t> frameLimits;

    bool has(const char* name) const { return letBinders.count(name) != 0; }
public:
    PTRef getOrUndef(const char* letSymbol) const {
        auto it = letBinders.find(letSymbol);
        if (it != letBinders.end()) {
            return it->second.getValue();
        }
        return PTRef_Undef;
    }
    void pushFrame() { frameLimits.push_back(knownBinders.size()); }
    void popFrame() {
        auto limit = frameLimits.back();
        frameLimits.pop_back();
        while (knownBinders.size() > limit) {
            const char* binder = knownBinders.back();
            knownBinders.pop_back();
            assert(this->has(binder));
            auto& values = letBinders.at(binder);
            if (values.hasShadowValue()) {
                values.restoreShadowedValue();
            } else {
                letBinders.erase(binder);
            }
        }
    }

    void addBinding(const char* name, PTRef arg) {
        knownBinders.push_back(name);
        if (not this->has(name)) {
            letBinders.insert(std::make_pair(name, LetBinder(arg)));
        } else {
            letBinders.at(name).addValue(arg);
        }
    }
};

class Interpret {
  protected:
    SMTConfig &     config;
    std::unique_ptr<Logic> logic;
    std::unique_ptr<MainSolver> main_solver;

    bool            f_exit;

    // Named terms for getting variable values
    MapWithKeys<const char*,PTRef,StringHash,Equal<const char*>> nameToTerm;
    VecMap<PTRef,const char*,PTRefHash,Equal<PTRef> > termToNames;
    vec<char*>      term_names; // For (! <t> :named <n>) constructs.  if Itp is enabled, this maps a
                                            // partition to it name.
    vec<PTRef>      assertions;
    vec<SymRef>     user_declarations;
    DefinedFunctions defined_functions;

    void                        initializeLogic(opensmt::Logic_t logicType);
    bool                        isInitialized() const { return logic != nullptr; }
    SRef                        sortFromASTNode(ASTNode const & n) const;
    static SortSymbol           sortSymbolFromASTNode(ASTNode const & node);

    void                        setInfo(ASTNode& n);
    void                        getInfo(ASTNode& n);
    void                        setOption(ASTNode& n);
    void                        getOption(ASTNode& n);
    void                        writeState(const char* fname);
    void                        writeSplits(const char* fname);
    bool                        declareFun(ASTNode const & n); //(const char* fname, const vec<SRef>& args);
    bool                        declareConst(ASTNode& n); //(const char* fname, const SRef ret_sort);
    bool                        defineFun(const ASTNode& n);
    bool                        checkSat();
    void                        getValue(const std::vector<ASTNode*>* term);
    void                        getModel();
    std::string                 printDefinitionSmtlib(PTRef tr, PTRef val);
    std::string                 printDefinitionSmtlib(const TemplateFunction &templateFun) const;
    void                        push(int);
    void                        pop(int);

    PTRef                       parseTerm(const ASTNode& term, LetRecords& letRecords);
    PTRef                       resolveTerm(const char* s, vec<PTRef>&& args, SRef sortRef = SRef_Undef, SymbolMatcher symbolMatcher = SymbolMatcher::Any);
    bool                        storeDefinedFun(std::string const & fname, const vec<PTRef>& args, SRef ret_sort, const PTRef tr);

    void                        exit();
    void                        getInterpolants(const ASTNode& n);
    void                        interp (ASTNode& n);

    void                        notify_formatted(bool error, const char* s, ...);
    void                        notify_success();
    void                        comment_formatted(const char* s, ...) const;

    bool                        addLetFrame(const vec<char *> & names, vec<PTRef> const& args, LetRecords& letRecords);
    PTRef                       letNameResolve(const char* s, const LetRecords& letRecords) const;
    PTRef                       resolveQualifiedIdentifier(const char * name, ASTNode const & sort, bool isQuoted);

    std::unique_ptr<MainSolver>   createMainSolver(const char* logic_name);

  public:

    Interpret(SMTConfig& c)
        : config     (c)
        , f_exit     (false)
        { }

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
    MainSolver&     getMainSolver() { return *main_solver; }
};

#endif
