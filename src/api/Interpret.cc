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


#include "Interpret.h"
#include "smt2tokens.h"
#include "ArithLogic.h"
#include "LogicFactory.h"
#include "Substitutor.h"

#include <string>
#include <sstream>
#include <cstdarg>
#include <unistd.h>

/***********************************************************
 * Class defining interpreter
 ***********************************************************/

PTRef
Interpret::getParsedFormula()
{
    PTRef root = main_solver->getLogic().mkAnd(assertions);
    return root;
}

void Interpret::setInfo(ASTNode const & n) {
    assert(n.getType() == ASTType::UATTR_T || n.getType() == ASTType::PATTR_T);

    std::string name;
    if (not n.hasValue()) {
        ASTNode const & an = *(*n.children)[0];
        assert(an.getType() == ASTType::UATTR_T || an.getType() == ASTType::PATTR_T);
        name = an.getValue();
    }
    else // Normal option
        name = n.getValue();

    config.setInfo(std::move(name), Info(n));
}

void Interpret::getInfo(ASTNode const & n) {
    assert(n.getType() == ASTType::INFO_T);
    assert(n.hasValue() or n.children->size() == 1);
    std::string const & name = n.hasValue() ? n.getValue() : (*(*n.children)[0]).getValue();

    const Info& value = config.getInfo(name);

    if (value.isEmpty())
        notify_formatted(true, "no value for info %s", name.c_str());
    else {
        auto val_str = value.toString();
        notify_formatted(false, "%s %s", name.c_str(), val_str.c_str());
    }
}

void Interpret::setOption(ASTNode const & n) {
    assert(n.getType() == ASTType::OPTION_T);
    assert(not n.hasValue() or not n.children->empty());
    std::string const & name = not n.hasValue() ? (*n.children)[0]->getValue() : n.getValue();

    SMTOption value(n);
    const char* msg = "ok";
    bool rval = config.setOption(name, value, msg);
    if (rval == false)
        notify_formatted(true, "set-option failed for %s: %s", name.c_str(), msg);
}

void Interpret::getOption(ASTNode const & n) {
    assert(n.getType() == ASTType::UATTR_T || n.getType() == ASTType::PATTR_T );

    assert(n.hasValue());
    std::string const & name = n.getValue();

    const SMTOption& value = config.getOption(name);

    if (value.isEmpty())
        notify_formatted(true, "No value for attr %s", name.c_str());
    else {
        auto str_val = value.toString();
        notify_formatted(false, "%s",str_val.c_str());
    }
}

void Interpret::exit() {
    f_exit = true;
}

using opensmt::Logic_t;
using opensmt::getLogicFromString;
using namespace osmttokens;

void Interpret::interp(ASTNode const & n) {
    assert(n.getType() == ASTType::CMD_T);
    const smt2token cmd = n.getToken();
    try {
        switch (cmd.x) {
            case t_setlogic: {
                ASTNode const & logic_n = *(*n.children)[0];
                std::string const & logic_name = logic_n.getValue();
                if (isInitialized()) {
                    notify_formatted(true, "logic has already been set to %s", main_solver->getLogic().getName().data());
                } else {
                    auto logic_type = getLogicFromString(logic_name);
                    if (logic_type == Logic_t::UNDEF) {
                        notify_formatted(true, "unknown logic %s", logic_name.c_str());
                        break;
                    }
                    initializeLogic(logic_type);
                    main_solver = createMainSolver(logic_name);
                    main_solver->initialize();
                    notify_success();
                }
                break;
            }
            case t_setinfo:
                setInfo(*(*n.children)[0]);
                notify_success();
                break;
            case t_setoption : {
                setOption(*(*n.children)[0]);
                notify_success();
                break;
            }
            case t_getinfo: {
                getInfo(*(*n.children)[0]);
                break;
            }
            case t_getoption: {
                getOption(*(*n.children)[0]);
                break;
            }
            case t_declaresort: {
                if (isInitialized()) {
                    assert(n.children->size() == 2);
                    ASTNode const & symbolNode = *(*n.children)[0];
                    assert(symbolNode.getType() == ASTType::SYM_T or symbolNode.getType() == ASTType::QSYM_T);
                    ASTNode const & numNode = *(*n.children)[1];
                    assert(numNode.getType() == ASTType::NUM_T);
                    int arity = std::stoi(numNode.getValue()); // MB: TODO: take care of out-of-range input
                    SortSymbol symbol(symbolNode.getValue(), arity);
                    SSymRef ssref;
                    if (logic->peekSortSymbol(symbol, ssref)) {
                        notify_formatted(true, "sort %s already declared", symbolNode.getValue().c_str());
                    } else {
                        logic->declareSortSymbol(std::move(symbol));
                        notify_success();
                    }
                } else
                    notify_formatted(true, "illegal command before set-logic: declare-sort");
                break;
            }
            case t_declarefun: {
                if (isInitialized()) {
                    if (declareFun(n))
                        notify_success();
                } else
                    notify_formatted(true, "Illegal command before set-logic: declare-fun");
                break;
            }
            case t_declareconst: {
                if (isInitialized()) {
                    declareConst(n);
                } else
                    notify_formatted(true, "Illegal command before set-logic: declare-const");
                break;
            }
            case t_assert: {
                if (isInitialized()) {
                    sstat status;
                    ASTNode const &asrt = *(*n.children)[0];
                    LetRecords letRecords;
                    PTRef tr = parseTerm(asrt, letRecords);
                    if (tr == PTRef_Undef)
                        notify_formatted(true, "assertion returns an unknown sort");
                    else {
                        assertions.push(tr);
                        char *err_msg = NULL;
                        status = main_solver->insertFormula(tr, &err_msg);

                        if (status == s_Error)
                            notify_formatted(true, "Error");
                        else if (status == s_Undef)
                            notify_success();
                        else if (status == s_False)
                            notify_success();

                        if (err_msg != NULL && status == s_Error)
                            notify_formatted(true, err_msg);
                        if (err_msg != NULL && status != s_Error)
                            comment_formatted(err_msg);
                        free(err_msg);
                    }
                } else {
                    notify_formatted(true, "Illegal command before set-logic: assert");
                }
                break;
            }
            case t_definefun: {
                if (isInitialized()) {
                    defineFun(n);
                } else {
                    notify_formatted(true, "Illegal command before set-logic: define-fun");
                }
                break;
            }
            case t_simplify: {
                if (isInitialized()) {
                    sstat status = main_solver->simplifyFormulas();
                    if (status == s_Error)
                        notify_formatted(true, "Simplify");
                } else {
                    notify_formatted(true, "Illegal command before set-logic: simplify");
                }
                break;
            }
            case t_checksat: {
                if (isInitialized()) {
                    checkSat();
                } else {
                    notify_formatted(true, "Illegal command before set-logic: check-sat");
                }
                break;
            }
            case t_getinterpolants: {
                if (config.produce_inter()) {
                    if (isInitialized()) {
                        getInterpolants(n);
                    } else {
                        notify_formatted(true, "Illegal command before set-logic: get-interpolants");
                    }
                } else {
                    notify_formatted(true,
                                     "Option to produce interpolants has not been set, skipping this command ...");
                }
                break;
            }
            case t_getassignment: {
                if (isInitialized()) {
                    getAssignment();
                } else {
                    notify_formatted(true, "Illegal command before set-logic: get-assignment");
                }
                break;
            }
            case t_getvalue: {
                if (not isInitialized()) {
                    notify_formatted(true, "Illegal command before set-logic: get-value");
                } else if (main_solver->getStatus() != s_True) {
                    notify_formatted(true, "Command get-value called, but solver is not in SAT state");
                } else {
                    getValue(*n.children);
                }
                break;
            }
            case t_getmodel: {
                if (not isInitialized()) {
                    notify_formatted(true, "Illegal command before set-logic: get-model");
                } else if (main_solver->getStatus() != s_True) {
                    notify_formatted(true, "Command get-model called, but solver is not in SAT state");
                } else {
                    getModel();
                }
                break;
            }

            case t_writestate: {
                if (not isInitialized()) {
                    notify_formatted(true, "Illegal command before set-logic: write-state");
                } else {
                    if (main_solver->solverEmpty()) {
                        sstat status = main_solver->simplifyFormulas();
                        if (status == s_Error)
                            notify_formatted(true, "write-state");
                    } else {
                        writeState((*n.children)[0]->getValue());
                    }
                }
                break;
            }
            case t_echo: {
                std::string const & str = (*n.children)[0]->getValue();
                notify_formatted(false, "%s", str.c_str());
                break;
            }
            case t_push: {
                if (not isInitialized()) {
                    notify_formatted(true, "Illegal command before set-logic: push");
                } else {
                    try {
                        int num = std::stoi((*n.children)[0]->getValue());
                        push(num);
                    } catch (std::out_of_range const & e) {
                        notify_formatted(true, "Illegal push command: %s", e.what());
                    }
                }
                break;
            }
            case t_pop: {
                if (not isInitialized()) {
                    notify_formatted(true, "Illegal command before set-logic: pop");
                } else {
                    try {
                        int num = std::stoi((*n.children)[0]->getValue());
                        pop(num);
                    } catch (std::out_of_range const &ex) {
                        notify_formatted(true, "Illegal pop command: %s", ex.what());
                    }
                }
                break;
            }
            case t_exit: {
                exit();
                notify_success();
                break;
            }
            default: {
                notify_formatted(true, "Unknown command encountered: %s", tokenToName.at(cmd.x).c_str());
            }
        }
    } catch (OsmtApiException const &e) {
        notify_formatted(true, e.what());
    }
}


bool Interpret::addLetFrame(std::vector<std::string> const & names, vec<PTRef> const& args, LetRecords& letRecords) {
    assert(names.size() == args.size_());
    if (names.size() > 1) {
        // check that they are pairwise distinct;
        std::unordered_set<std::string> namesAsSet(names.begin(), names.end());
        if (namesAsSet.size() != names.size()) {
            comment_formatted("Overloading let variables makes no sense");
            return false;
        }
    }
    for (unsigned int i = 0; i < names.size(); ++i) {
        std::string const & name = names[i];
        if (logic->hasSym(name.c_str()) && logic->getSym(logic->symNameToRef(name.c_str())[0]).noScoping()) {
            comment_formatted("Names marked as no scoping cannot be overloaded with let variables: %s", name.c_str());
            return false;
        }
        letRecords.addBinding(name.c_str(), args[i]);
    }
    return true;
}

//
// Determine whether the term refers to some let definition
//
PTRef Interpret::letNameResolve(const char* s, const LetRecords& letRecords) const {
    return letRecords.getOrUndef(s);
}

PTRef Interpret::resolveQualifiedIdentifier(const char * name, ASTNode const & sort, bool isQuoted) {
    SRef sr = sortFromASTNode(sort);
    PTRef tr = PTRef_Undef;
    try {
        tr = resolveTerm(name, {}, sr, isQuoted ? SymbolMatcher::Uninterpreted : SymbolMatcher::Any);
    } catch (OsmtApiException & e) {
        reportError(e.what());
    }
    return tr;
}

PTRef Interpret::resolveTerm(const char* s, vec<PTRef>&& args, SRef sortRef, SymbolMatcher symbolMatcher) {
    if (defined_functions.has(s)) {
        auto const & tpl = defined_functions[s];
        return logic->instantiateFunctionTemplate(tpl, std::move(args));
    }
    return logic->resolveTerm(s, std::move(args), sortRef, symbolMatcher);
}

PTRef Interpret::parseTerm(const ASTNode& term, LetRecords& letRecords) {
    ASTType t = term.getType();
    if (t == ASTType::TERM_T) {
        std::string const & name = (*term.children)[0]->getValue();
//        comment_formatted("Processing term %s", name);
        PTRef tr = PTRef_Undef;
        try {
            tr = logic->mkConst(name.c_str());
        } catch (OsmtApiException const & e) {
            comment_formatted("While processing %s: %s", name.c_str(), e.what());
        }
        return tr;
    }

    else if (t == ASTType::QID_T) {
        if ((*term.children)[0]->getType() == ASTType::AS_T) {
            ASTNode const & as_node = *(*term.children)[0];
            ASTNode const & symbolNode = *(*as_node.children)[0];
            bool isQuoted = symbolNode.getType() == ASTType::QSYM_T;
            std::string const & name = (*as_node.children)[0]->getValue();
            ASTNode const & sortNode = *(*as_node.children)[1];
            assert(not name.empty());
            PTRef tr = resolveQualifiedIdentifier(name.c_str(), sortNode, isQuoted);
            return tr;
        } else {
            ASTNode const & symbolNode = *(*term.children)[0];
            std::string const & name = symbolNode.getValue();
            bool isQuoted = symbolNode.getType() == ASTType::QSYM_T;
            PTRef tr = letNameResolve(name.c_str(), letRecords);
            if (tr != PTRef_Undef) {
                return tr;
            } try {
                tr = resolveTerm(name.c_str(), {}, SRef_Undef, isQuoted ? SymbolMatcher::Uninterpreted : SymbolMatcher::Any);
            } catch (OsmtApiException & e) {
                reportError(e.what());
            }
            return tr;
        }
    }

    else if ( t == ASTType::LQID_T ) {
        // Multi-argument term
        assert(term.children->size() > 1);
        auto const & astArgs = opensmt::span(&(*term.children)[1], term.children->size()-1);
        std::string const & name = (*term.children)[0]->getValue();
        vec<PTRef> args;
        for (auto const & arg : astArgs) {
            PTRef arg_tr = parseTerm(*arg, letRecords);
            if (arg_tr == PTRef_Undef) {
                return PTRef_Undef;
            } else {
                args.push(arg_tr);
            }
        }

        assert(args.size() > 0);

        PTRef tr = PTRef_Undef;
        try {
            tr = resolveTerm(name.c_str(), std::move(args));
        } catch (ArithDivisionByZeroException &ex) {
            reportError(ex.what());
        } catch (OsmtApiException &e) {
            reportError(e.what());
        }
        return tr;
    } else if (t == ASTType::LET_T) {
        assert(term.children->size() == 2);
        std::vector<std::unique_ptr<ASTNode>> const & varList = *(*term.children)[0]->children;
        ASTNode const & letBoundedTerm = *(*term.children)[1];
        vec<PTRef> tmp_args;
        std::vector<std::string> names;

        // use RAII idiom to guard the scope of new LetFrame (and ensure the cleaup of names)
        class Guard {
            LetRecords& rec;
        public:
            Guard(LetRecords& rec): rec(rec) { rec.pushFrame(); }
            ~Guard() { rec.popFrame(); }
        } scopeGuard(letRecords);
        // First read the term declarations in the let statement
        for (auto const & varListEl : varList) {
            PTRef let_tr = parseTerm(*(*(*varListEl).children)[0], letRecords);
            if (let_tr == PTRef_Undef) return PTRef_Undef;
            tmp_args.push(let_tr);
            names.push_back(varListEl->getValue());
        }

        // Only then insert them to the table
        bool success = addLetFrame(names, tmp_args, letRecords);
        if (not success) {
            comment_formatted("Let name addition failed");
            return PTRef_Undef;
        }
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(letBoundedTerm, letRecords);
        if (tr == PTRef_Undef) {
            comment_formatted("Failed in parsing the let scoped term");
            return PTRef_Undef;
        }
        return tr;
    }

    else if (t == ASTType::BANG_T) {
        assert(term.children->size() == 2);

        ASTNode const & named_term = *(*term.children)[0];
        ASTNode const & attr_l = *(*term.children)[1];
        assert(attr_l.getType() == ASTType::GATTRL_T);
        assert(attr_l.children->size() == 1);
        ASTNode const & name_attr = *(*attr_l.children)[0];

        PTRef tr = parseTerm(named_term, letRecords);
        if (tr == PTRef_Undef) return tr;

        if (name_attr.getValue() == ":named") {
            ASTNode const & sym = *(*name_attr.children)[0];
            assert(sym.getType() == ASTType::SYM_T or sym.getType() == ASTType::QSYM_T);
            if (nameToTerm.find(sym.getValue()) != nameToTerm.end()) {
                notify_formatted(true, "name %s already exists", sym.getValue().c_str());
                return PTRef_Undef;
            }
            std::string name = sym.getValue();
            // MB: term_names becomes the owner of the string and is responsible for deleting
            term_names.push_back(name);
            nameToTerm.insert({name, tr});
        }
        return tr;
    }
    else
        comment_formatted("Unknown term type");
    return PTRef_Undef;
}

sstat Interpret::checkSat() {
    sstat res;
    res = main_solver->check();

    if (res == s_True) {
        notify_formatted(false, "sat");
    }
    else if (res == s_False)
        notify_formatted(false, "unsat");
    else
        notify_formatted(false, "unknown");

    const Info& status = config.getInfo(":status");
    if (!status.isEmpty()) {
        std::string statusString = status.toString();
        if ((statusString.compare("sat") == 0) && (res == s_False)) {
            notify_formatted(false, "(error \"check status which says sat\")");

        }
        else if ((statusString.compare("unsat") == 0) && (res == s_True)) {
            notify_formatted(false, "(error \"check status which says unsat\")");
        }
    }

    if (res == s_Undef) {
        const SMTOption& o_dump_state = config.getOption(":dump-state");
        const SpType o_split = config.sat_split_type();
        std::string name = config.dump_state();
        if (!o_dump_state.isEmpty() && o_split == spt_none)
            writeState(name);
    }

    return res;
}

void Interpret::push(int n) {
    if (not config.isIncremental()) {
        notify_formatted(true, "push encountered but solver not in incremental mode");
    } else {
        if (n < 0) {
            notify_formatted(true, "Incorrect push command, value is negative.");
        } else {
            while (n--) {
                defined_functions.pushScope();
                main_solver->push();
            }
            notify_success();
        }
    }
}

void Interpret::pop(int n) {
    if (config.isIncremental()) {
        if (n < 0) {
            notify_formatted(true, "Incorrect pop command, value is negative.");
        } else {
            bool success = true;
            while (n-- and success) {
                success = main_solver->pop();
                if (success) { defined_functions.popScope(); }
            }
            if (success) {
                notify_success();
            } else {
                notify_formatted(true, "Attempt to pop beyond the top of the stack");
            }
        }
    } else {
        notify_formatted(true, "pop encountered but solver not in incremental mode");
    }
}

bool Interpret::getAssignment() {
    if (not isInitialized()) {
       notify_formatted(true, "Illegal command before set-logic");
       return false;
    }
    if (main_solver->getStatus() != s_True) {
       notify_formatted(true, "Last solver call not satisfiable");
       return false;
    }
    std::stringstream ss;
    ss << '(';
    for (unsigned int i = 0; i < term_names.size(); i++) {
        std::string const & name = term_names[i];
        PTRef tr = nameToTerm[name.c_str()];
        lbool val = main_solver->getTermValue(tr);
        ss << '(' << name << ' ' << (val == l_True ? "true" : (val == l_False ? "false" : "unknown"))
            << ')' << (i < term_names.size() - 1 ? " " : "");
    }
    ss << ')';
    const std::string& out = ss.str();
    notify_formatted(false, out.c_str());
    return true;
}

void Interpret::getValue(std::vector<std::unique_ptr<ASTNode>> const & terms)
{
    auto model = main_solver->getModel();
    Logic& logic = main_solver->getLogic();
    std::vector<opensmt::pair<PTRef,PTRef>> values;
    for (auto const & term : terms) {
        LetRecords tmp;
        PTRef tr = parseTerm(*term, tmp);
        if (tr != PTRef_Undef) {
            values.emplace_back(opensmt::pair<PTRef,PTRef>{tr, model->evaluate(tr)});
            auto pt_str = logic.printTerm(tr);
            comment_formatted("Found the term %s", pt_str.c_str());
        } else
            comment_formatted("Error parsing the term %s", (*term->children)[0]->getValue().c_str());
    }
    printf("(");
    for (auto const & valPair : values) {
        auto name = logic.printTerm(valPair.first);
        auto value = logic.printTerm(valPair.second);
        printf("(%s %s)", name.c_str(), value.c_str());
    }
    printf(")\n");
}

namespace {
/*
 * This is a helper class to work around the limitation of ModelValidator
 * which does not like formal parameter with the same name as a variable already defined in the model previously.
 */
class NameClashResolver {
public:
    NameClashResolver(Logic & logic) : logic(logic) {}

    void addForbiddenVar(PTRef var) {
        assert(logic.isVar(var));
        forbiddenVars.insert(var);
    }

    void addFunction(SymRef sym) {
        functionsToCheck.insert(sym);
    }

    std::vector<TemplateFunction> getSafeTemplates(Model const & model) {
        std::vector<TemplateFunction> res;
        unsigned num = 0;
        for (SymRef symRef : functionsToCheck) {
            auto const & modelTemplate = model.getDefinition(symRef);
            if (hasClash(modelTemplate)) {
                auto const & oldArgs = modelTemplate.getArgs();
                vec<PTRef> newArgs; newArgs.capacity(oldArgs.size());
                Logic::SubstMap substMap;
                for (PTRef oldArg : oldArgs) {
                    std::string name;
                    PTRef var = PTRef_Undef;
                    do {
                        name = getSafePrefix(symRef) + std::to_string(num++);
                        var = logic.mkVar(logic.getSortRef(oldArg), name.c_str());
                    } while (forbiddenVars.find(var) != forbiddenVars.end());
                    newArgs.push(var);
                    substMap.insert(oldArg, var);
                }
                FunctionSignature templateSig(logic.protectName(symRef), std::move(newArgs), logic.getSortRef(symRef));
                PTRef newBody = Substitutor(logic, substMap).rewrite(modelTemplate.getBody());
                res.emplace_back(std::move(templateSig), newBody);

            } else {
                res.push_back(modelTemplate);
            }
        }
        return res;
    }
private:
    Logic & logic;
    std::unordered_set<PTRef, PTRefHash> forbiddenVars;
    std::unordered_set<SymRef, SymRefHash> functionsToCheck;

    bool hasClash(TemplateFunction const & templateFunction) {
        auto const & args = templateFunction.getArgs();
        return std::any_of(args.begin(), args.end(), [this](PTRef arg) {
            return forbiddenVars.find(arg) != forbiddenVars.end();
        });
    }

    std::string getSafePrefix(SymRef symref) {
        return logic.getSymName(symref)[0] == 'x' ? "y!" : "x!";
    }
};
}

void Interpret::getModel() {

    auto model = main_solver->getModel();
    NameClashResolver resolver(*logic);
    std::stringstream ss;
    ss << "(\n";
    for (SymRef symref : user_declarations) {
        const Symbol & sym = logic->getSym(symref);
        if (sym.nargs() == 0) {
            // variable, just get its value
            const char* s = logic->getSymName(symref);
            SRef symSort = sym.rsort();
            PTRef term = logic->mkVar(symSort, s);
            resolver.addForbiddenVar(term);
            PTRef val = model->evaluate(term);
            ss << printDefinitionSmtlib(term, val);
        } else {
            // function
            resolver.addFunction(symref);
        }
    }
    for (auto const & safeTempl : resolver.getSafeTemplates(*model)) {
        ss << printDefinitionSmtlib(safeTempl);
    }
    ss << ')';
    std::cout << ss.str() << std::endl;
}

/**
 *
 * @param tr the term to print
 * @param val its value
 * @return the term value in an smtlib2 compliant format
 * Example:
 * (; U is sort of cardinality 2
 *   (define-fun a () U
 *     (as @0 U))
 *   (define-fun b () U
 *     (as @1 U))
 *   (define-fun f ((x U)) U
 *     (ite (= x (as @1 U)) (as @0 U)
 *       (as @1 U))
 *   )
 * )
 */
std::string Interpret::printDefinitionSmtlib(PTRef tr, PTRef val) {
    std::stringstream ss;
    auto s = logic->protectName(logic->getSymRef(tr));
    SRef sortRef = logic->getSym(tr).rsort();
    ss << "  (define-fun " << s << " () " << logic->printSort(sortRef) << '\n';
    ss << "    " << logic->printTerm(val) << ")\n";
    return ss.str();
}

std::string Interpret::printDefinitionSmtlib(TemplateFunction const & templateFun) const {
    std::stringstream ss;
    ss << "  (define-fun " << templateFun.getName() << " (";
    vec<PTRef> const & args = templateFun.getArgs();
    for (int i = 0; i < args.size(); i++) {
        auto sortString = logic->printSort(logic->getSortRef(args[i]));
        ss << "(" << logic->protectName(logic->getSymRef(args[i])) << " " << sortString << ")" << (i == args.size()-1 ? "" : " ");
    }
    ss << ")" << " " << logic->printSort(templateFun.getRetSort()) << "\n";
    ss << "    " << logic->printTerm(templateFun.getBody()) << ")\n";
    return ss.str();
}

void Interpret::writeState(std::string const & filename)
{
    char* msg;
    bool rval;

    rval = main_solver->writeSolverState_smtlib2(filename.c_str(), &msg);

    if (!rval) {
        notify_formatted("%s", msg);
    }
}

bool Interpret::declareFun(ASTNode const & n) // (const char* fname, const vec<SRef>& args)
{
    assert(n.children->size() == 3);
    ASTNode const & name_node = *(*n.children)[0];
    ASTNode const & args_node = *(*n.children)[1];
    ASTNode const & ret_node = *(*n.children)[2];

    std::string const & fname = name_node.getValue();

    vec<SRef> args;

    SRef retSort = sortFromASTNode(ret_node);
    if (retSort != SRef_Undef) {
        args.push(retSort);
    } else {
        notify_formatted(true, "Unknown return sort %s of %s", sortSymbolFromASTNode(ret_node).name.c_str(), fname.c_str());
        return false;
    }

    for (auto const & childNode : *(args_node.children)) {
        SRef argSort = sortFromASTNode(*childNode);
        if (argSort != SRef_Undef) {
            args.push(argSort);
        } else {
            notify_formatted(true, "Undefined sort %s in function %s", sortSymbolFromASTNode(*childNode).name.c_str(), fname.c_str());
            return false;
        }
    }

    SRef rsort = args[0];
    vec<SRef> args2;

    for (int i = 1; i < args.size(); i++)
        args2.push(args[i]);

    SymRef rval = logic->declareFun(fname, rsort, args2);

    if (rval == SymRef_Undef) {
        comment_formatted("Error while declare-fun %s", fname.c_str());
        return false;
    }
    user_declarations.push(rval);
    return true;
}

bool Interpret::declareConst(ASTNode const & n) //(const char* fname, const SRef ret_sort)
{
    assert(n.children->size() == 3);
    ASTNode const & name_node = *(*n.children)[0];
    // n.children[1] is the args node, which is empty
    ASTNode const & ret_node = *(*n.children)[2];

    std::string const & fname = name_node.getValue();
    SRef ret_sort = sortFromASTNode(ret_node);
    if (ret_sort == SRef_Undef) {
        notify_formatted(true, "Failed to declare constant %s", fname.c_str());
        notify_formatted(true, "Unknown return sort %s of %s", sortSymbolFromASTNode(ret_node).name.c_str(), fname.c_str());
        return false;
    }

    SymRef rval = logic->declareFun(fname, ret_sort, {});
    if (rval == SymRef_Undef) {
        comment_formatted("Error while declare-const %s", fname.c_str());
        return false;
    }
    user_declarations.push(rval);
    notify_success();
    return true;
}

bool Interpret::defineFun(const ASTNode& n)
{
    assert(n.children->size() == 4);

    ASTNode const & name_node = *(*n.children)[0];
    ASTNode const & args_node = *(*n.children)[1];
    ASTNode const & ret_node = *(*n.children)[2];
    ASTNode const & term_node = *(*n.children)[3];

    std::string const & fname = name_node.getValue();

    // Get the argument sorts
    vec<SRef> arg_sorts;
    vec<PTRef> arg_trs;
    for (auto const & childNode : *(args_node.children)) {
        assert(childNode->children->size() == 1);
        std::string varName = childNode->getValue();
        ASTNode const & sortNode = *(*childNode->children)[0];
        SRef sortRef = sortFromASTNode(sortNode);
        if (sortRef == SRef_Undef) {
            notify_formatted(true, "Undefined sort %s in function %s", sortSymbolFromASTNode(sortNode).name.c_str(), fname.c_str());
            return false;
        }
        arg_sorts.push(sortRef);
        PTRef pvar = logic->mkVar(arg_sorts.last(), varName.c_str());
        arg_trs.push(pvar);
    }

    // The return sort
    SRef ret_sort = sortFromASTNode(ret_node);
    if (ret_sort == SRef_Undef) {
        notify_formatted(true, "Unknown return sort %s of %s", sortSymbolFromASTNode(ret_node).name.c_str(), fname.c_str());
        return false;
    }
    sstat status;
    LetRecords letRecords;
    PTRef tr = parseTerm(term_node, letRecords);
    if (tr == PTRef_Undef) {
        notify_formatted(true, "define-fun returns an unknown sort");
        return false;
    }
    else if (logic->getSortRef(tr) != ret_sort) {
        notify_formatted(true, "define-fun term and return sort do not match: %s and %s\n", logic->printSort(logic->getSortRef(tr)).c_str(), logic->printSort(ret_sort).c_str());
        return false;
    }
    bool rval = storeDefinedFun(fname, arg_trs, ret_sort, tr);
    if (rval) notify_success();
    else {
        notify_formatted(true, "define-fun failed");
        return false;
    }

    return rval;
}

bool Interpret::storeDefinedFun(std::string const & fname, const vec<PTRef> & args, SRef ret_sort, const PTRef tr) {
    if (defined_functions.has(fname)) { return false; }

    bool scoped = not config.declarations_are_global();
    defined_functions.insert(fname, TemplateFunction(fname, args, ret_sort, tr), scoped);
    return true;
}


void Interpret::comment_formatted(const char* fmt_str, ...) const {
    va_list ap;
    int d;
    char c1, *t;
    if (config.verbosity() < 2) return;
    std::cout << "; ";

    va_start(ap, fmt_str);
    while (true) {
        c1 = *fmt_str++;
        if (c1 == '%') {
            switch (*fmt_str++) {
            case 's':
                t = va_arg(ap, char *);
                std::cout << t;
                break;
            case 'd':
                d = va_arg(ap, int);
                std::cout << d;
                break;
            case '%':
                std::cout << '%';
                break;
            }
        }
        else if (c1 != '\0')
            std::cout << c1;
        else break;
    }
    va_end(ap);
    std::cout << std::endl;
}


void Interpret::notify_formatted(bool error, const char* fmt_str, ...) {
    va_list ap;
    int d;
    char c1, *t;
    if (error)
        std::cout << "(error \"";

    va_start(ap, fmt_str);
    while (true) {
        c1 = *fmt_str++;
        if (c1 == '%') {
            switch (*fmt_str++) {
            case 's':
                t = va_arg(ap, char *);
                std::cout << t;
                break;
            case 'd':
                d = va_arg(ap, int);
                std::cout << d;
                break;
            case '%':
                std::cout << '%';
                break;
            }
        }
        else if (c1 != '\0')
            std::cout << c1;
        else break;
    }
    va_end(ap);
    if (error)
        std::cout << "\")" << '\n';
    std::cout << std::endl;
}

void Interpret::notify_success() {
    if (config.printSuccess()) {
        std::cout << "success" << std::endl;
    }
}

void Interpret::execute(ASTNode const & r) {
    for (auto const & command : *r.children) {
        if (f_exit) break;
        interp(*command);
    }
}

int Interpret::interpFile(FILE* in) {
    Smt2newContext context(in);
    int rval = yyparse(&context);

    if (rval != 0) return rval;

    const ASTNode & r = context.getRoot();
    execute(r);
    return rval;
}

int Interpret::interpFile(char *content){
    Smt2newContext context(content);
    int rval = yyparse(&context);

    if (rval != 0) return rval;
    ASTNode const & r = context.getRoot();
    execute(r);
    return rval;
}


// For reading from pipe
int Interpret::interpPipe() {

    int buf_sz  = 16;
    char* buf   = (char*) malloc(sizeof(char)*buf_sz);
    int rd_head = 0;
    int par     = 0;
    int i       = 0;

    bool inComment = false;
    bool inString = false;
    bool inQuotedSymbol = false;

    bool done  = false;
    buf[0] = '\0';
    while (!done) {
        assert(i >= 0 and i <= rd_head);
        assert(buf[rd_head] == '\0');
        assert(rd_head < buf_sz);
        if (rd_head == buf_sz - 1) {
            buf_sz *= 2;
            buf = (char*) realloc(buf, sizeof(char)*buf_sz);
        }
        int rd_chunk = buf_sz - rd_head - 1;
        assert(rd_chunk > 0);
        int bts_rd = read(STDIN_FILENO, &buf[rd_head], rd_chunk);
        if (bts_rd == 0) {
            // Read EOF
            break;
        }
        if (bts_rd < 0) {
            // obtain the error string
            char const * err_str = strerror(errno);
            // format the error
            notify_formatted(true, err_str);
            break;
        }

        rd_head += bts_rd;
        buf[rd_head] = '\0';

        for (; i < rd_head; i++) {

            char c = buf[i];

            if (inComment || (not inQuotedSymbol and not inString and c == ';')) {
                inComment = (c != '\n');
            }
            if (inComment) {
                continue;
            }
            assert(not inComment);
            if (inQuotedSymbol) {
                inQuotedSymbol = (c != '|');
            } else if (not inString and c == '|') {
                inQuotedSymbol = true;
            }
            if (inQuotedSymbol) {
                continue;
            }
            assert (not inComment and not inQuotedSymbol);
            if (inString) {
                inString = (c != '\"');
            } else if (c == '\"') {
                inString = true;
            }
            if (inString) {
                continue;
            }

            if (c == '(') {
                par ++;
            }
            else if (c == ')') {
                par --;
                if (par == 0) {
                    // prepare parse buffer
                    char* buf_out = (char*) malloc(sizeof(char)*i+2);
                    // copy contents to the parse buffer
                    for (int j = 0; j <= i; j++)
                        buf_out[j] = buf[j];
                    buf_out[i+1] = '\0';

                    // copy the part after a top-level balanced parenthesis to the start of buf
                    for (int j = i+1; j < rd_head; j++)
                        buf[j-i-1] = buf[j];
                    buf[rd_head-i-1] = '\0';

                    // update the end position of buf to reflect the removal of the string to be parsed
                    rd_head = rd_head-i-1;

                    i = -1; // will be incremented to 0 by the loop condition.
                    Smt2newContext context(buf_out);
                    int rval = yyparse(&context);
                    if (rval != 0)
                        notify_formatted(true, "scanner");
                    else {
                        ASTNode const & r = context.getRoot();
                        execute(r);
                        done = f_exit;
                    }
                    free(buf_out);
                }
                if (par < 0) {
                    notify_formatted(true, "pipe reader: unbalanced parentheses");
                    done = true;
                }
            }
        }
    }
    free(buf);
    return 0;
}

SortSymbol Interpret::sortSymbolFromASTNode(ASTNode const & node) {
    auto type = node.getType();
    if (type == ASTType::SYM_T or type == ASTType::QSYM_T) {
        return {node.getValue(), 0};
    } else {
        assert(type == ASTType::LID_T and not node.children->empty());
        ASTNode const & name = *(*node.children)[0];
        return {name.getValue(), static_cast<unsigned int>(node.children->size() - 1)};
    }
}

SRef Interpret::sortFromASTNode(ASTNode const & node) const {
    auto type = node.getType();
    if (type == ASTType::SYM_T or type == ASTType::QSYM_T) {
        SortSymbol symbol(node.getValue(), 0);
        SSymRef symRef;
        bool known = logic->peekSortSymbol(symbol, symRef);
        if (not known) { return SRef_Undef; }
        return logic->getSort(symRef, {});
    } else {
        assert(type == ASTType::LID_T and not node.children->empty());
        ASTNode const & name = *(*node.children)[0];
        SortSymbol symbol(name.getValue(), node.children->size() - 1);
        SSymRef symRef;
        bool known = logic->peekSortSymbol(symbol, symRef);
        if (not known) { return SRef_Undef; }
        vec<SRef> args;
        auto astArgs = opensmt::span(&(*node.children)[1], node.children->size()-1);
        for (auto const & astArg : astArgs) {
            SRef argSortRef = sortFromASTNode(*astArg);
            if (argSortRef == SRef_Undef) { return SRef_Undef; }
            args.push(argSortRef);
        }
        return logic->getSort(symRef, std::move(args));
    }
    assert(type == ASTType::LID_T and not node.children->empty());
    ASTNode const & name = *(*node.children)[0];
    SortSymbol symbol(name.getValue(), node.children->size() - 1);
    SSymRef symRef;
    bool known = logic->peekSortSymbol(symbol, symRef);
    if (not known) { return SRef_Undef; }
    vec<SRef> args;
    auto astSortArgs = opensmt::span(&(*node.children)[1], node.children->size()-1);
    for (auto const & astSortArg : astSortArgs) {
        SRef argSortRef = sortFromASTNode(*astSortArg);
        if (argSortRef == SRef_Undef) { return SRef_Undef; }
        args.push(argSortRef);
    }
    return logic->getSort(symRef, std::move(args));
}

void Interpret::getInterpolants(const ASTNode& n)
{
    auto const & exps = n.children;
    vec<PTRef> grouping; // Consists of PTRefs that we want to group
    LetRecords letRecords;
    letRecords.pushFrame();
    for (auto const & key : term_names) {
        letRecords.addBinding(key, nameToTerm[key]);
    }

    for (auto const & c : *exps) {
        PTRef tr = parseTerm(*c, letRecords);
//        printf("Itp'ing a term %s\n", logic->pp(tr));
        grouping.push(tr);
    }
    letRecords.popFrame();

    if (!(config.produce_inter() > 0))
        throw OsmtApiException("Cannot interpolate");

    assert(grouping.size() >= 2);
    std::vector<ipartitions_t> partitionings;
    ipartitions_t p = 0;
    // We assume that together the groupings cover all query, so we ignore the last argument, since that should contain all that was missing at that point
    for (int i = 0; i < grouping.size() - 1; i++)
    {
        PTRef group = grouping[i];
        if (is_top_level_assertion(group))
        {
            int assertion_index = get_assertion_index(group);
            assert(assertion_index >= 0);
            opensmt::setbit(p, static_cast<unsigned int>(assertion_index));
        }
        else {
            bool ok = group != PTRef_Undef && logic->isAnd(group);
            if (ok) {
                Pterm const & and_t = logic->getPterm(group);
                for (int j = 0; j < and_t.size(); j++) {
                    PTRef tr = and_t[j];
                    ok = is_top_level_assertion(tr);
                    if (!ok) { break; }
                    int assertion_index = get_assertion_index(tr);
                    assert(assertion_index >= 0);
                    opensmt::setbit(p, static_cast<unsigned int>(assertion_index));
                }
            }
            if (!ok) {
                // error in interpolation command
                notify_formatted(true, "Invalid arguments of get-interpolants command");
                return;
            }
        }
        partitionings.emplace_back(p);
    }
    if (main_solver->getStatus() != s_False) {
        notify_formatted(true, "Cannot interpolate, solver is not in UNSAT state!");
        return;
    }
    auto interpolationContext = main_solver->getInterpolationContext();
//        cerr << "Computing interpolant with mask " << p << endl;
    vec<PTRef> itps;
    if (partitionings.size() > 1) {
        interpolationContext->getPathInterpolants(itps, partitionings);
    } else {
        interpolationContext->getSingleInterpolant(itps, partitionings[0]);
    }

    for (int j = 0; j < itps.size(); j++) {
        auto itp = logic->pp(itps[j]);
        notify_formatted(false, "%s%s%s",
                         (j == 0 ? "(" : " "), itp.c_str(), (j == itps.size() - 1 ? ")" : ""));
    }
}

bool Interpret::is_top_level_assertion(PTRef ref) {
    return get_assertion_index(ref) >= 0;
}

int Interpret::get_assertion_index(PTRef ref) {
    for (int i = 0; i < assertions.size(); ++i) {
        if (ref == assertions[i]) { return i;}
    }
    return -1;
}

void Interpret::initializeLogic(opensmt::Logic_t logicType) {
    logic.reset(opensmt::LogicFactory::getInstance(logicType));
}

std::unique_ptr<MainSolver> Interpret::createMainSolver(std::string const & logic_name) {
    return std::make_unique<MainSolver>(*logic, config, logic_name + " solver");
}



