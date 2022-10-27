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
    bool has(std::string const & name) const { return defined_functions.find(name) != defined_functions.end(); }

    void insert(std::string const & name, TemplateFunction && templ, bool scoped = false) {
        assert(not has(name));
        defined_functions[name] = std::move(templ);
        if (scoped) { scopedNames.push(name); }
    }

    TemplateFunction & operator[](char const * name) {
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
    std::unordered_map<std::string, LetBinder> letBinders;
    std::vector<std::string> knownBinders;
    std::vector<std::size_t> frameLimits;

    bool has(std::string const & name) const { return letBinders.find(name) != letBinders.end(); }
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
            std::string binder = knownBinders.back();
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

    void addBinding(std::string const & name, PTRef arg) {
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
    std::unordered_map<std::string,PTRef> nameToTerm;
    std::vector<std::string> term_names; // For (! <t> :named <n>) constructs.  if Itp is enabled, this maps a
                                            // partition to it name.
    vec<PTRef>      assertions;
    vec<SymRef>     user_declarations;
    DefinedFunctions defined_functions;

    void                        initializeLogic(opensmt::Logic_t logicType);
    bool                        isInitialized() const { return logic != nullptr; }

    void                        writeState(std::string const & fname);
    std::string                 printDefinitionSmtlib(PTRef tr, PTRef val);
    std::string                 printDefinitionSmtlib(const TemplateFunction &templateFun) const;

    PTRef                       parseTerm(TermNode const & term, LetRecords& letRecords);
    PTRef                       parseTerm(NormalTermNode const * term, LetRecords & letRecords);
    PTRef                       parseTerm(LetTermNode const * term, LetRecords & letRecords);
    PTRef                       parseTerm(ForallNode const * term, LetRecords & letRecords);
    PTRef                       parseTerm(ExistsNode const * term, LetRecords & letRecords);
    PTRef                       parseTerm(AnnotationNode const * term, LetRecords & letRecords);
    PTRef                       resolveTerm(const char* s, vec<PTRef>&& args, SRef sortRef = SRef_Undef, SymbolMatcher symbolMatcher = SymbolMatcher::Any);
    bool                        storeDefinedFun(std::string const & fname, const vec<PTRef>& args, SRef ret_sort, const PTRef tr);

    virtual void                exit();
    void                        interp(CommandNode const * n);
    void                        interp(SetLogic const & n);
    void                        interp(SetInfo const & n);
    void                        interp(SetOption const & n);
    void                        interp(GetInfo const & n);
    void                        interp(GetOption const & n);
    void                        interp(DeclareSort const & n);
    void                        interp(DeclareFun const & n);
    void                        interp(DeclareConst const & n);
    void                        interp(AssertNode const & n);
    void                        interp(DefineFun const & n);
    void                        interp(Simplify const & n);
    void                        interp(CheckSatNode const & n);
    void                        interp(GetInterpolants const & n);
    void                        interp(GetAssignment const & n);
    void                        interp(GetValue const & n);
    void                        interp(GetModel const & n);
    void                        interp(Echo const & n);
    void                        interp(PushNode const & n);
    void                        interp(PopNode const & n);
    void                        interp(Exit const & n);
    void                        notify_formatted(bool error, const char* s, ...);
    void                        notify_success();
    void                        comment_formatted(const char* s, ...) const;

    bool                        addLetFrame(std::vector<std::string> const & names, vec<PTRef> const& args, LetRecords& letRecords);
    PTRef                       letNameResolve(const char* s, const LetRecords& letRecords) const;
    PTRef                       resolveQualifiedIdentifier(std::string const & name, SortNode const & sort, bool isQuoted);
    SRef sortFromSortNode(SortNode const & node) const;

    virtual std::unique_ptr<MainSolver>   createMainSolver(std::string const & logic_name);

  public:

    Interpret(SMTConfig & c)
        : config     (c)
        , f_exit     (false)
        { }

    int interpFile(FILE* in);
    int interpFile(char *content);
    int interpPipe();

    bool    gotExit() const { return f_exit; }

    void    reportError(char const * msg) { notify_formatted(true, msg); }

    PTRef getParsedFormula();
    vec<PTRef>& getAssertions() { return assertions; }
    bool is_top_level_assertion(PTRef ref);
    int get_assertion_index(PTRef ref);
    MainSolver&     getMainSolver() { return *main_solver; }
};

#endif
