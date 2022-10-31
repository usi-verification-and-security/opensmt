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
#include "ParseNodePrinter.h"

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

void Interpret::interp(SetInfo const & n) {
    config.setInfo(n.getName(), SMTOption{n.getValue()});
    notify_success();
}

void Interpret::interp(GetInfo const & n) {
    assert(n.key);
    std::string const & name = *n.key;

    auto const & value = config.getInfo(name);

    if (value.type == ConstType::empty)
        notify_formatted(true, "no value for info %s", name.c_str());
    else {
        auto val_str = value.toString();
        notify_formatted(false, "%s %s", name.c_str(), val_str.c_str());
    }
}

void Interpret::interp(SetOption const & n) {
    assert(n.option);
    switch (n.option->type) {
    case OptionNode::OptionType::Attribute: {
        auto val = std::get_if<std::unique_ptr<AttributeNode>>(&n.option->value);
        assert(val);
        assert(*val);
        try {
            config.setOption(*(**val).name, SMTOption{*(**val).value});
        } catch (std::out_of_range & e) {
            notify_formatted(true, "Overflow in %s", opensmt::nodeToString()(*(**val).value).c_str());
            return;
        } catch (OsmtApiException & e) {
            notify_formatted(true, "%s", e.what());
            return;
        }
        break;
    }
    case OptionNode::OptionType::DiagnosticOutputChannel: {
        auto val = std::get_if<std::unique_ptr<std::string>>(&n.option->value);
        assert(val);
        assert(*val);
        config.setOption(":diagnostic-output-channel", SMTOption{std::move(**val)});
        break;
    }
    case OptionNode::OptionType::ExpandDefinitions: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":expand-definitions", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::InteractiveMode: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":interactive-mode", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::PrintSuccess: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":print-success", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::ProduceAssignments: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":produce-assignments", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::ProduceModels: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":produce-models", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::ProduceProofs: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":produce-proofs", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::ProduceUnsatCores: {
        auto val = std::get_if<bool>(&n.option->value);
        assert(val);
        config.setOption(":produce-unsat-cores", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::RandomSeed: {
        auto val = std::get_if<int>(&n.option->value);
        assert(val);
        config.setOption(":random-seed", SMTOption{*val});
        break;
    }
    case OptionNode::OptionType::RegularOutputChannel: {
        auto val = std::get_if<std::unique_ptr<std::string>>(&n.option->value);
        assert(val);
        assert(*val);
        config.setOption(":regular-output-channel", SMTOption{std::move(**val)});
        break;
    }
    case OptionNode::OptionType::Verbosity: {
        auto val = std::get_if<int>(&n.option->value);
        assert(val);
        config.setOption(":verbosity", SMTOption{*val});
        break;
    }
    default:
        notify_formatted(true, "unknown option");
        return;
    }
    notify_success();
}

void Interpret::interp(GetOption const & n) {
    assert(n.key);
    std::string const & name = *n.key;

    const SMTOption& value = config.getOption(name);

    if (value.isEmpty())
        notify_formatted(true, "No value for option %s", name.c_str());
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

void Interpret::interp(CommandNode const * n) {
    if (auto setLogic = dynamic_cast<SetLogic const *>(n)) {
        return interp(*setLogic);
    } else if (auto setInfo = dynamic_cast<SetInfo const *>(n)) {
        return interp(*setInfo);
    } else if (auto setOption = dynamic_cast<SetOption const *>(n)) {
        return interp(*setOption);
    } else if (auto getInfo = dynamic_cast<GetInfo const *>(n)) {
        return interp(*getInfo);
    } else if (auto getOption = dynamic_cast<GetOption const *>(n)) {
        return interp(*getOption);
    } else if (auto declareSort = dynamic_cast<DeclareSort const *>(n)) {
        return interp(*declareSort);
    } else if (auto declareFun = dynamic_cast<DeclareFun const *>(n)) {
        return interp(*declareFun);
    } else if (auto declareConst = dynamic_cast<DeclareConst const *>(n)) {
        return interp(*declareConst);
    } else if (auto assertNode = dynamic_cast<AssertNode const *>(n)) {
        return interp(*assertNode);
    } else if (auto defineFun = dynamic_cast<DefineFun const *>(n)) {
        return interp(*defineFun);
    } else if (auto simplify = dynamic_cast<Simplify const *>(n)) {
        return interp(*simplify);
    } else if (auto checkSatNode = dynamic_cast<CheckSatNode const *>(n)) {
        return interp(*checkSatNode);
    } else if (auto getInterpolants = dynamic_cast<GetInterpolants const *>(n)) {
        return interp(*getInterpolants);
    } else if (auto getAssignment = dynamic_cast<GetAssignment const *>(n)) {
        return interp(*getAssignment);
    } else if (auto getValue = dynamic_cast<GetValue const *>(n)) {
        return interp(*getValue);
    } else if (auto getModel = dynamic_cast<GetModel const *>(n)) {
        return interp(*getModel);
    } else if (auto echo = dynamic_cast<Echo const *>(n)) {
        return interp(*echo);
    } else if (auto pushNode = dynamic_cast<PushNode const *>(n)) {
        return interp(*pushNode);
    } else if (auto popNode = dynamic_cast<PopNode const *>(n)) {
        return interp(*popNode);
    } else if (auto exit = dynamic_cast<Exit const *>(n)) {
        return interp(*exit);
    } else {
        notify_formatted(true, "Unimplemented command");
    }
}

void Interpret::interp(SetLogic const & n) {
    std::string const & logic_name = n.getLogicName();
    if (isInitialized()) {
        notify_formatted(true, "logic has already been set to %s", main_solver->getLogic().getName().data());
    } else {
        auto logic_type = getLogicFromString(logic_name);
        if (logic_type == Logic_t::UNDEF) {
            notify_formatted(true, "unknown logic %s", logic_name.c_str());
            return;
        }
        initializeLogic(logic_type);
        main_solver = createMainSolver(logic_name);
        main_solver->initialize();
        notify_success();
    }
}

void Interpret::interp(DeclareSort const & declareSort) {
    if (not isInitialized()) {
        notify_formatted(true, "illegal command before set-logic: declare-sort");
        return;
    }
    SymbolNode const & symbolNode = *declareSort.symbol;
    std::string const & numNode = *declareSort.num;
    int arity = std::stoi(numNode); // MB: TODO: take care of out-of-range input
    SortSymbol symbol(opensmt::nodeToString()(symbolNode), arity);
    SSymRef ssref;
    if (logic->peekSortSymbol(symbol, ssref)) {
        notify_formatted(true, "sort %s already declared", opensmt::nodeToString()(symbolNode).c_str());
    } else {
        logic->declareSortSymbol(std::move(symbol));
        notify_success();
    }
}

void Interpret::interp(AssertNode const & n) {
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: assert");
        return;
    }

    sstat status;
    TermNode const & asrt = *n.term;
    LetRecords letRecords;
    PTRef tr = parseTerm(asrt, letRecords);
    if (tr == PTRef_Undef) {
        notify_formatted(true, "assertion returns an unknown sort");
    } else {
        assertions.push(tr);
        char *err_msg = nullptr;
        status = main_solver->insertFormula(tr, &err_msg);

        if (status == s_Error)
            notify_formatted(true, "Error");
        else if (status == s_Undef)
            notify_success();
        else if (status == s_False)
            notify_success();

        if (err_msg != nullptr && status == s_Error)
            notify_formatted(true, err_msg);
        if (err_msg != nullptr && status != s_Error)
            comment_formatted(err_msg);
        free(err_msg);
    }
}

void Interpret::interp(Simplify const &) {
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: simplify");
        return;
    }
    sstat status = main_solver->simplifyFormulas();
    if (status == s_Error) {
        notify_formatted(true, "Simplify");
    } else {
        notify_success();
    }
}

void Interpret::interp(CheckSatNode const &) {
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: check-sat");
        return;
    }
    (void)checkSat();
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

    auto const & status = config.getInfo(":status");
    if (!status.isEmpty()) {
        std::string statusString = status.toString();
        if (statusString == "sat" && (res == s_False)) {
            notify_formatted(false, "(error \"check status which says sat\")");
        }
        else if (statusString == "unsat" && (res == s_True)) {
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

void Interpret::interp(GetModel const &) {
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: get-model");
        return;
    } else if (main_solver->getStatus() != s_True) {
        notify_formatted(true, "Command get-model called, but solver is not in SAT state");
        return;
    }

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

void Interpret::interp(Echo const & n) {
    std::string const & str = *n.text;
    notify_formatted(false, "%s", str.c_str());
}

void Interpret::interp(PushNode const & n) {
    if (not config.isIncremental()) {
        notify_formatted(true, "push encountered but solver not in incremental mode");
        return;
    } else if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: push");
        return;
    } else if (n.num < 0) {
        notify_formatted(true, "Incorrect push command, value is negative.");
        return;
    }
    int num = n.num;
    while (num --) {
        defined_functions.pushScope();
        main_solver->push();
    }
    notify_success();
}

void Interpret::interp(PopNode const & n) {
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: pop");
        return;
    } else if (not config.isIncremental()) {
        notify_formatted(true, "pop encountered but solver not in incremental mode");
        return;
    } else if (n.num < 0) {
        notify_formatted(true, "Incorrect pop command, value is negative.");
        return;
    }
    bool success = true;
    int num = n.num;
    while (num -- and success) {
        success = main_solver->pop();
        if (success) { defined_functions.popScope(); }
    }
    if (success) {
        notify_success();
    } else {
        notify_formatted(true, "Attempt to pop beyond the top of the stack");
    }
}

void Interpret::interp(Exit const &) {
    exit();
    notify_success();
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

PTRef Interpret::resolveQualifiedIdentifier(std::string const & name, SortNode const & sort, bool isQuoted) {
    SRef sr = sortFromSortNode(sort);
    PTRef tr = PTRef_Undef;
    try {
        tr = resolveTerm(name.c_str(), {}, sr, isQuoted ? SymbolMatcher::Uninterpreted : SymbolMatcher::Any);
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

PTRef Interpret::parseTerm(LetTermNode const * letTerm, LetRecords & letRecords) {
    assert(letTerm->arguments->size() == 1);
    auto const & varList = *letTerm->bindings;
    auto const & letBoundedTerm = (*letTerm->arguments)[0];
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
        PTRef let_tr = parseTerm(*varListEl->term, letRecords);
        if (let_tr == PTRef_Undef) return PTRef_Undef;
        tmp_args.push(let_tr);
        names.push_back(opensmt::nodeToString()(*varListEl->symbol));
    }

    // Only then insert them to the table
    bool success = addLetFrame(names, tmp_args, letRecords);
    if (not success) {
        comment_formatted("Let name addition failed");
        return PTRef_Undef;
    }
    // This is now constructed with the let declarations context in let_branch
    PTRef tr = parseTerm(*letBoundedTerm, letRecords);
    if (tr == PTRef_Undef) {
        comment_formatted("Failed in parsing the let scoped term");
        return PTRef_Undef;
    }
    return tr;
}

PTRef Interpret::parseTerm(AnnotationNode const * term, LetRecords & letRecords) {
    TermNode const & named_term = *(*term->arguments)[0];
    PTRef tr = parseTerm(named_term, letRecords);
    if (tr == PTRef_Undef) return tr;

    auto const & attr_l = *term->attributes;

    for (auto const & attribute : attr_l) {
        std::string const & name_attr = *attribute->name;

        if (name_attr == ":named") {
            auto name = opensmt::nodeToString()(*attribute->value);
            if (nameToTerm.find(name) != nameToTerm.end()) {
                notify_formatted(true, "name %s already exists", name.c_str());
                return PTRef_Undef;
            }
            // MB: term_names becomes the owner of the string and is responsible for deleting
            term_names.push_back(name);
            nameToTerm.insert({name, tr});
        }
    }
    return tr;
}

PTRef Interpret::parseTerm(TermNode const & term, LetRecords& letRecords) {
   if (auto const regularTerm = dynamic_cast<NormalTermNode const*>(&term)) {
       return parseTerm(regularTerm, letRecords);
    } else if (auto const letTerm = dynamic_cast<LetTermNode const *>(&term)) {
        return parseTerm(letTerm, letRecords);
    } else if (auto const annotatedTerm = dynamic_cast<AnnotationNode const *>(&term)) {
        return parseTerm(annotatedTerm, letRecords);
    } else if (auto const forallTerm = dynamic_cast<ForallNode const *>(&term)) {
        return parseTerm(forallTerm, letRecords);
    } else if (auto const existsTerm = dynamic_cast<ExistsNode const *>(&term)) {
        return parseTerm(existsTerm, letRecords);
    }
    comment_formatted("Unknown term type");
    return PTRef_Undef;
}

PTRef Interpret::parseTerm(NormalTermNode const * term, LetRecords & letRecords) {
    if (auto constName = std::get_if<std::unique_ptr<SpecConstNode>>(&term->head)) {
        auto const & name = *(*constName)->value;
        try {
            PTRef tr = logic->mkConst(name.c_str());
            return tr;
        } catch (OsmtApiException const & e) {
            comment_formatted("While processing %s: %s", name.c_str(), e.what());
            return PTRef_Undef;
        }
    }
    auto identifier = std::get_if<std::unique_ptr<IdentifierNode>>(&term->head);
    assert(identifier);
    auto name = opensmt::nodeToString()(*(*identifier)->symbol);
    bool isQuoted = (*identifier)->symbol->quoted;
    if (term->returnSort) {
        return resolveQualifiedIdentifier(name, *term->returnSort, isQuoted);
    } else {
        if (not term->arguments) {
            PTRef tr = letNameResolve(name.c_str(), letRecords);
            if (tr != PTRef_Undef) {
                return tr;
            } try {
                tr = resolveTerm(name.c_str(), {}, SRef_Undef, isQuoted ? SymbolMatcher::Uninterpreted : SymbolMatcher::Any);
            } catch (OsmtApiException & e) {
                reportError(e.what());
            }
            return tr;
        } else {
            vec<PTRef> args;
            for (auto const & arg : *term->arguments) {
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
        }
    }
}

PTRef Interpret::parseTerm(ForallNode const *, LetRecords &) {
    return PTRef_Undef;
}
PTRef Interpret::parseTerm(ExistsNode const *, LetRecords &) {
    return PTRef_Undef;
}





void Interpret::interp(GetAssignment const &) {
    if (not isInitialized()) {
       notify_formatted(true, "Illegal command before set-logic");
    }
    if (main_solver->getStatus() != s_True) {
       notify_formatted(true, "Last solver call not satisfiable");
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
}

namespace {
// Todo: implement all cases
std::string printTermNode(TermNode const & term) {
    auto term_p = dynamic_cast<NormalTermNode const *>(&term);
    assert(term_p);
    if (auto const_p = std::get_if<std::unique_ptr<SpecConstNode>>(&term_p->head)) {
        return *(*const_p)->value;
    } else {
        auto head_p = std::get_if<std::unique_ptr<IdentifierNode>>(&term_p->head);
        assert(head_p);
        return opensmt::nodeToString()(*(*head_p)->symbol);
    }
}
}

void Interpret::interp(GetValue const & getValue)
{
    auto model = main_solver->getModel();
    Logic & logic = *(this->logic);
    std::vector<opensmt::pair<PTRef,PTRef>> values;
    for (auto const term : *getValue.terms) {
        LetRecords tmp;
        PTRef tr = parseTerm(*term, tmp);
        if (tr != PTRef_Undef) {
            values.emplace_back(opensmt::pair<PTRef,PTRef>{tr, model->evaluate(tr)});
            auto pt_str = logic.printTerm(tr);
            comment_formatted("Found the term %s", pt_str.c_str());
        } else
            comment_formatted("Error parsing the term %s", printTermNode(*term).c_str());
    }
    printf("(");
    for (auto const & valPair : values) {
        auto name = logic.printTerm(valPair.first);
        auto value = logic.printTerm(valPair.second);
        printf("(%s %s)", name.c_str(), value.c_str());
    }
    printf(")\n");
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



void Interpret::interp(DeclareFun const & n) // (const char* fname, const vec<SRef>& args)
{
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: declare-fun");
        return;
    }
    SymbolNode const & name_node = *n.name;
    auto const & args_vec = *n.argumentSorts;
    SortNode const & ret_sort = *n.returnSort;

    std::string const & fname = opensmt::nodeToString()(name_node);

    vec<SRef> args;

    SRef retSort = sortFromSortNode(ret_sort);
    if (retSort != SRef_Undef) {
        args.push(retSort);
    } else {
        notify_formatted(true, "Unknown return sort %s of %s", opensmt::nodeToString()(*ret_sort.identifier).c_str(), fname.c_str());
        return;
    }

    for (auto const childNode : args_vec) {
        SRef argSort = sortFromSortNode(*childNode);
        if (argSort != SRef_Undef) {
            args.push(argSort);
        } else {
            notify_formatted(true, "Undefined sort %s in function %s", opensmt::nodeToString()(*childNode->identifier).c_str(), fname.c_str());
            return;
        }
    }

    SRef rsort = args[0];
    vec<SRef> args2;

    for (int i = 1; i < args.size(); i++)
        args2.push(args[i]);

    SymRef rval = logic->declareFun(fname, rsort, args2);

    if (rval == SymRef_Undef) {
        comment_formatted("Error while declare-fun %s", fname.c_str());
        return;
    }
    user_declarations.push(rval);
    notify_success();
}


void Interpret::interp(DeclareConst const & n) //(const char* fname, const SRef ret_sort)
{
    auto const & name_node = *n.name;
    auto const & ret_node = *n.sort;

    std::string const & fname = opensmt::nodeToString()(name_node);
    SRef ret_sort = sortFromSortNode(ret_node);
    if (ret_sort == SRef_Undef) {
        notify_formatted(true, "Failed to declare constant %s", fname.c_str());
        notify_formatted(true, "Unknown return sort %s of %s", opensmt::nodeToString()(ret_node).c_str(), fname.c_str());
        return;
    }

    SymRef rval = logic->declareFun(fname, ret_sort, {});
    if (rval == SymRef_Undef) {
        comment_formatted("Error while declare-const %s", fname.c_str());
        return;
    }
    user_declarations.push(rval);
    notify_success();
}

void Interpret::interp(DefineFun const & n) {
    if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: define-fun");
        return;
    }
    SymbolNode const & nameNode = *n.name;
    auto const & argumentVector = *n.args;
    SortNode const & returnSort = *n.returnSort;
    TermNode const & termNode = *n.term;

    std::string const & fname = opensmt::nodeToString()(nameNode);

    // Get the argument sorts
    vec<SRef> arg_sorts;
    vec<PTRef> arg_trs;
    for (auto const & sortedVar_p : argumentVector) {
        std::string const & varName = opensmt::nodeToString()(*sortedVar_p->symbol);
        SortNode const & sortNode = *sortedVar_p->sort;
        SRef sortRef = sortFromSortNode(sortNode);
        if (sortRef == SRef_Undef) {
            notify_formatted(true, "Undefined sort %s in function %s", opensmt::nodeToString()(sortNode).c_str(), fname.c_str());
            return;
        }
        arg_sorts.push(sortRef);
        PTRef pvar = logic->mkVar(arg_sorts.last(), varName.c_str());
        arg_trs.push(pvar);
    }

    // The return sort
    SRef ret_sort = sortFromSortNode(returnSort);
    if (ret_sort == SRef_Undef) {
        notify_formatted(true, "Unknown return sort %s of %s", opensmt::nodeToString()(returnSort).c_str(), fname.c_str());
        return;
    }
    sstat status;
    LetRecords letRecords;
    PTRef tr = parseTerm(termNode, letRecords);
    if (tr == PTRef_Undef) {
        notify_formatted(true, "define-fun returns an unknown sort");
        return;
    }
    else if (logic->getSortRef(tr) != ret_sort) {
        notify_formatted(true, "define-fun term and return sort do not match: %s and %s\n", logic->printSort(logic->getSortRef(tr)).c_str(), logic->printSort(ret_sort).c_str());
        return;
    }
    bool rval = storeDefinedFun(fname, arg_trs, ret_sort, tr);
    if (rval) {
        notify_success();
    } else {
        notify_formatted(true, "define-fun failed");
        return;
    }
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

int Interpret::interpFile(FILE* in) {
    Smt2newContext context(in);
    int rval = yyparse(&context);
    if (context.hasRoot()) {
        for (auto command : context.getRoot()) {
            if (rval == 0 and not f_exit) { interp(command); }
            delete command;
        }
    }
    return rval;
}

int Interpret::interpFile(char *content){
    Smt2newContext context(content);
    int rval = yyparse(&context);

    if (rval != 0) return rval;
//    ASTNode const & r = context.getRoot();
//    execute(r);
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
                        for (auto command : context.getRoot()) {
                            if (rval == 0 and not f_exit) { interp(command); }
                            delete command;
                        }
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

SRef Interpret::sortFromSortNode(SortNode const & node) const {
    SortSymbol symbol(opensmt::nodeToString()(*node.identifier->symbol), node.sortList->size());
    SSymRef symRef;
    bool known = logic->peekSortSymbol(symbol, symRef);
    if (not known) { return SRef_Undef; }
    vec<SRef> args;
    for (auto const arg : *node.sortList) {
        SRef argSortRef = sortFromSortNode(*arg);
        if (argSortRef == SRef_Undef) { return SRef_Undef; }
        args.push(argSortRef);
    }
    return logic->getSort(symRef, std::move(args));
}

void Interpret::interp(GetInterpolants const & n) {
    if (not config.produce_inter()) {
        notify_formatted(true, "Option to produce interpolants has not been set, skipping this command ...");
        return;
    } else if (not isInitialized()) {
        notify_formatted(true, "Illegal command before set-logic: get-interpolants");
        return;
    }
    auto const & exps = n.configuration;
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

    if (not config.produce_inter())
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



