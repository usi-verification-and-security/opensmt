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


#ifndef SMT2NEWCONTEXT_H
#define SMT2NEWCONTEXT_H

#include <iostream>
#include <variant>
#include "SMTConfig.h"

enum class ConstType {
    numeral,
    decimal,
    hexadecimal,
    binary,
    string
};

class GeneralNode {};

struct SpecConstNode : public GeneralNode {
    ConstType type;
    std::string value;
};

struct SymbolNode : public GeneralNode {
   std::variant<std::string,SpecConstNode> name;
   bool quoted;
};

struct SExpr : public GeneralNode {
    std::variant<SpecConstNode,SymbolNode,std::string,std::vector<SExpr*>> data;
};

struct AttributeValueNode : public GeneralNode {
    std::variant<SpecConstNode, SymbolNode, std::vector<SExpr*>> value;
    AttributeValueNode(SpecConstNode && n) : value(std::move(n)) {}
    AttributeValueNode(SymbolNode && n) : value(std::move(n)) {}
    AttributeValueNode(std::vector<SExpr*> n) : value(std::move(n)) {}
};

struct AttributeNode : public GeneralNode {
    bool predefined = false;
    std::string name;
    AttributeValueNode value;
};

struct IdentifierNode : public GeneralNode {
    SymbolNode symbol;
    std::vector<std::string> numeralList;
};


class OptionNode : public GeneralNode { };

struct PrintSuccess : public OptionNode { bool value; };
struct ExpandDefinitions : public OptionNode { bool value; };
struct InteractiveMode : public OptionNode { bool value; };
struct ProduceProofs : public OptionNode { bool value; };
struct ProduceUnsatCores : public OptionNode { bool value; };
struct ProduceModels : public OptionNode { bool value; };
struct ProduceAssignments : public OptionNode { bool value; };
struct RegularOutputChannel : public OptionNode { std::string value; };
struct DiagnosticOutputChannel : public OptionNode { std::string value; };
struct RandomSeed : public OptionNode { int value; };
struct Verbosity : public OptionNode { int value; };
struct Attribute : public OptionNode { AttributeNode value; };

class CommandNode : public GeneralNode {};

class SetLogic : public CommandNode {
    SymbolNode logic;
public:
    SetLogic(SymbolNode && logic) : logic(std::move(logic)) {}
};

class SetOption : public CommandNode {
    OptionNode option;
public:
    SetOption(OptionNode && option) : option(std::move(option)) {}
};

class SetInfo : public CommandNode {
    AttributeNode attribute;
public:
    SetInfo(AttributeNode && attribute) : attribute(std::move(attribute)) {}
};

class DeclareSort : public CommandNode {
    SymbolNode symbol;
    std::string num;
public:
    DeclareSort(SymbolNode && symbol, std::string && num) : symbol(std::move(symbol)), num(std::move(num)) {}
};

struct SortNode : public GeneralNode {
    IdentifierNode identifier;
};


struct ComplexSortNode : public SortNode {
    SortNode * sort;
    std::vector<SortNode *> sortList;
};

struct QualIdentifierNode : public GeneralNode {
    IdentifierNode identifier;
    SortNode * returnSort = nullptr;
};

class DefineSort : public CommandNode {
    SymbolNode name;
    std::vector<SymbolNode> argumentSorts;
    SortNode sort;
public:
    DefineSort(SymbolNode && name, std::vector<SymbolNode> && argumentSorts, SortNode && sort)
        : name(std::move(name))
        , argumentSorts(std::move(argumentSorts))
        , sort(std::move(sort))
        {}
};

class DeclareFun : public CommandNode {
    SymbolNode name;
    std::vector<SortNode*> argumentSorts;
    SortNode returnSort;
public:
    DeclareFun(SymbolNode && name, std::vector<SortNode*> && argumentSorts, SortNode && returnSort)
        : name(std::move(name))
        , argumentSorts(std::move(argumentSorts))
        , returnSort(std::move(returnSort))
        {}
};

class DeclareConst : public CommandNode {
    std::variant<SymbolNode,SpecConstNode> name;
    SortNode sort;
public:
    DeclareConst(SymbolNode && name, SortNode && sort) : name(std::move(name)), sort(std::move(sort)) {}
    DeclareConst(SpecConstNode && name, SortNode && sort) : name(std::move(name)), sort(std::move(sort)) {}
};

class TermNode : public GeneralNode {};

class NormalTermNode : public TermNode {
    std::variant<SpecConstNode,IdentifierNode> head;
    SortNode * returnSort = nullptr;
    std::vector<TermNode*> arguments;
public:
    NormalTermNode(SpecConstNode && head) : head(std::move(head)) {}
    NormalTermNode(IdentifierNode && head, SortNode * returnSort, std::vector<TermNode*> && arguments)
        : head(std::move(head))
        , returnSort(returnSort)
        , arguments(std::move(arguments))
    {}
    SortNode * getSortIfKnown() { return returnSort; }
};

struct VarBindingNode : public GeneralNode {
    SymbolNode symbol;
    TermNode term;
};

struct LetTermNode : public TermNode {
    TermNode term;
    std::vector<VarBindingNode> bindings;
};

struct SortedVarNode : public GeneralNode {
    SymbolNode symbol;
    SortNode sort;
};

struct ForallNode : public TermNode {
    TermNode term;
    std::vector<SortedVarNode> bindings;
};

struct ExistsNode : public TermNode {
    TermNode term;
    std::vector<SortedVarNode> bindings;
};

struct AnnotationNode : public TermNode {
    TermNode term;
    std::vector<AttributeNode> attributes;
};

struct DefineFun : public CommandNode {
    SymbolNode name;
    std::vector<SortedVarNode> args;
    SortNode returnSort;
    TermNode term;
};

struct PushNode : public CommandNode { int num; };

struct PopNode : public CommandNode { int num; };

struct AssertNode : public CommandNode { TermNode term; };

struct CheckSatNode : public CommandNode {};

struct GetAssertions : public CommandNode {};

struct GetProof : public CommandNode {};

struct GetInterpolants : public CommandNode { std::vector<TermNode*> configuration; };

struct GetUnsatCore : public CommandNode {};

struct GetValue : public CommandNode { std::vector<TermNode*> terms; };

struct GetModel : public CommandNode {};

struct GetAssignment : public CommandNode {};

struct GetOption : public CommandNode { std::string key; };

struct GetInfo : public CommandNode { std::string key; };

struct Simplify : public CommandNode {};

struct Exit : public CommandNode {};

struct Echo : public CommandNode { std::string text; };

class Smt2newContext {
  private:
    int                         init_scanner();
    void                        destroy_scanner();
    char*                       buffer;
    int                         buffer_sz;
    int                         buffer_cap;
    std::vector<CommandNode*>   root;
  public:
    void*                       scanner;
    int                         result;
    FILE*                       is;
    char*                       ib;
    bool                        interactive;
    inline std::vector<CommandNode*> const & getRoot() { return root; };

    Smt2newContext(FILE* in) :
       buffer_sz(0)
     , buffer_cap(1)
     , result(0)
     , is(in)
     , ib(nullptr)
     , interactive(false)
    {
        init_scanner();
        buffer = (char *)malloc(buffer_cap);
    }

    Smt2newContext(char* in_s) :
       buffer_sz(0)
     , buffer_cap(1)
     , result(0)
     , is(nullptr)
     , ib(in_s)
     , interactive(true)
    {
        init_scanner();
        buffer = (char*) malloc(buffer_cap);
    }

    ~Smt2newContext() {
        destroy_scanner();
        free(buffer);
    }

    void insertBuf(char c) {
        if (buffer_cap < buffer_sz + 1) {
            buffer_cap *= 2;
            buffer = (char*) realloc(buffer, buffer_cap);
        }
        buffer[buffer_sz++] = c;
    }

    const char* getBuf() {
        insertBuf('\0');
        return buffer;
    }

    void clearBuf() {
        buffer_sz = 0;
    }

    void insertRoot(std::vector<CommandNode*> && n) {
        root = std::move(n);
    }

};

int yyparse(Smt2newContext*);

#endif
