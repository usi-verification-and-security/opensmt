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
    std::unique_ptr<std::string> value;
};

struct SymbolNode : public GeneralNode {
    std::variant<std::unique_ptr<std::string>,std::unique_ptr<SpecConstNode>> name;
    bool quoted;
};

struct SExpr : public GeneralNode {
    std::variant<std::unique_ptr<SpecConstNode>,std::unique_ptr<SymbolNode>,std::unique_ptr<std::string>,std::unique_ptr<std::vector<SExpr*>>> data;
    ~SExpr() {
        struct Qel {
            SExpr * node;
            uint32_t processed;
        };
        std::vector<Qel> queue;
        queue.emplace_back(Qel{this, static_cast<uint32_t>(0)});
        while (not queue.empty()) {
            auto & [node, processed] = queue.back();
            auto children = std::get_if<std::unique_ptr<std::vector<SExpr *>>>(&node->data);
            if (children and processed < (*children)->size()) {
                ++processed;
                queue.emplace_back(Qel{(**children)[processed - 1], 0});
            }
            assert(not children or processed == (*children)->size());
            assert(node);
            delete node;
            queue.pop_back();
        }
    }
};

struct AttributeValueNode : public GeneralNode {
    std::variant<std::unique_ptr<SpecConstNode>, std::unique_ptr<SymbolNode>, std::unique_ptr<std::vector<SExpr*>>> value;
    AttributeValueNode(std::unique_ptr<SpecConstNode> && node) : value(std::move(node)) {}
    AttributeValueNode(std::unique_ptr<SymbolNode> && node) : value(std::move(node)) {}
    AttributeValueNode(std::unique_ptr<std::vector<SExpr*>> && node) : value(std::move(node)) {}
    ~AttributeValueNode() {
        if (auto vec = std::get_if<std::unique_ptr<std::vector<SExpr*>>>(&value)) {
            for (auto el : (**vec)) {
                delete el;
            }
        }
    }
};

struct AttributeNode : public GeneralNode {
    bool predefined = false;
    std::unique_ptr<std::string> name;
    std::unique_ptr<AttributeValueNode> value;
};

struct IdentifierNode : public GeneralNode {
    std::unique_ptr<SymbolNode> symbol;
    std::unique_ptr<std::vector<std::string>> numeralList;
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

struct SetLogic : public CommandNode { std::unique_ptr<SymbolNode> logic; };
struct SetOption : public CommandNode { std::unique_ptr<OptionNode> option; };
struct SetInfo : public CommandNode { std::unique_ptr<AttributeNode> attribute; };

struct DeclareSort : public CommandNode {
    std::unique_ptr<SymbolNode> symbol;
    std::unique_ptr<std::string> num;
};

struct SortNode : public GeneralNode {
    std::unique_ptr<IdentifierNode> identifier;
    std::unique_ptr<std::vector<SortNode *>> sortList;

    ~SortNode() {
        struct Qel {
           SortNode * node;
           uint32_t processed;
        };
        std::vector<Qel> queue;
        queue.emplace_back(Qel{this, static_cast<uint32_t>(0)});
        while (not queue.empty()) {
            auto & [node, processed] = queue.back();
            auto & children = *node->sortList;
            if (processed < children.size()) {
                ++processed;
                queue.emplace_back(Qel{children[processed - 1], 0});
            }
            assert(processed == children.size());
            assert(node);
            for (auto child : *sortList) {
                assert(child->sortList->empty());
                delete child;
            }
            node->sortList->clear(); // delete is not called on the pointers
            queue.pop_back();
        }
    }
};

struct QualIdentifierNode : public GeneralNode {
    std::unique_ptr<IdentifierNode> identifier;
    std::unique_ptr<SortNode> returnSort = nullptr;
};

struct DefineSort : public CommandNode {
    std::unique_ptr<SymbolNode> name;
    std::unique_ptr<std::vector<std::unique_ptr<SymbolNode>>> argumentSorts;
    std::unique_ptr<SortNode> sort;
};

struct DeclareFun : public CommandNode {
    std::unique_ptr<SymbolNode> name;
    std::unique_ptr<std::vector<SortNode*>> argumentSorts;
    std::unique_ptr<SortNode> returnSort;
    ~DeclareFun() {
        for (auto sort : *argumentSorts) {
            delete sort;
        }
    }
};

struct DeclareConst : public CommandNode {
    std::variant<std::unique_ptr<SymbolNode>,std::unique_ptr<SpecConstNode>> name;
    std::unique_ptr<SortNode> sort;
};

struct SortedVarNode : public GeneralNode {
    std::unique_ptr<SymbolNode> symbol;
    std::unique_ptr<SortNode> sort;
};

struct TermNode;

struct VarBindingNode : public GeneralNode {
    std::unique_ptr<SymbolNode> symbol;
    TermNode * term;
};

struct TermNode : public GeneralNode {
    std::unique_ptr<std::vector<TermNode*>> arguments;
    TermNode(std::unique_ptr<std::vector<TermNode*>> && arguments) : arguments(std::move(arguments)) {}
    virtual ~TermNode();
};

struct NormalTermNode : public TermNode {
    std::variant<std::unique_ptr<SpecConstNode>,std::unique_ptr<IdentifierNode>> head;
    std::unique_ptr<SortNode> returnSort = nullptr;
    // Todo: understand why I need this constructor
    NormalTermNode(std::unique_ptr<std::vector<TermNode*>> && arguments,
                   std::variant<std::unique_ptr<SpecConstNode>,
                   std::unique_ptr<IdentifierNode>> && head,
                   std::unique_ptr<SortNode> && returnSort)
        :  TermNode(std::move(arguments)), head(std::move(head)), returnSort(std::move(returnSort)) {}
};

struct LetTermNode : public TermNode {
    std::unique_ptr<std::vector<std::unique_ptr<VarBindingNode>>> bindings;
    LetTermNode(TermNode * term, std::unique_ptr<std::vector<std::unique_ptr<VarBindingNode>>> && bindings)
        : TermNode{std::make_unique<std::vector<TermNode*>>(std::vector<TermNode*>{term})}
        , bindings(std::move(bindings))
    {}
};

struct ForallNode : public TermNode {
    std::unique_ptr<std::vector<SortedVarNode>> quantified;
    ForallNode(TermNode * term, std::unique_ptr<std::vector<SortedVarNode>> && quantified)
        : TermNode{std::make_unique<std::vector<TermNode*>>(std::vector<TermNode*>{term})}
        , quantified(std::move(quantified)) {}
};

struct ExistsNode : public TermNode {
    std::unique_ptr<std::vector<SortedVarNode>> quantified;
    ExistsNode(TermNode * term, std::unique_ptr<std::vector<SortedVarNode>> && quantified)
        : TermNode{std::make_unique<std::vector<TermNode*>>(std::vector<TermNode*>{term})}
        , quantified(std::move(quantified)) {}
};

struct AnnotationNode : public TermNode {
    std::unique_ptr<std::vector<AttributeNode>> attributes;
    AnnotationNode(TermNode * term, std::unique_ptr<std::vector<AttributeNode>> && attributes)
        : TermNode{std::make_unique<std::vector<TermNode*>>(std::vector<TermNode*>{term})}
        , attributes(std::move(attributes)) {}
};

struct DefineFun : public CommandNode {
    std::unique_ptr<SymbolNode> name;
    std::unique_ptr<std::vector<SortedVarNode>> args;
    std::unique_ptr<SortNode> returnSort;
    std::unique_ptr<TermNode> term;
};

struct PushNode : public CommandNode { int num; };

struct PopNode : public CommandNode { int num; };

struct AssertNode : public CommandNode { std::unique_ptr<TermNode> term; };

struct CheckSatNode : public CommandNode {};

struct GetAssertions : public CommandNode {};

struct GetProof : public CommandNode {};

struct GetInterpolants : public CommandNode { std::unique_ptr<std::vector<TermNode*>> configuration; };

struct GetUnsatCore : public CommandNode {};

struct GetValue : public CommandNode { std::unique_ptr<std::vector<TermNode*>> terms; };

struct GetModel : public CommandNode {};

struct GetAssignment : public CommandNode {};

struct GetOption : public CommandNode { std::unique_ptr<std::string> key; };

struct GetInfo : public CommandNode { std::unique_ptr<std::string> key; };

struct Simplify : public CommandNode {};

struct Exit : public CommandNode {};

struct Echo : public CommandNode { std::unique_ptr<std::string> text; };

class Smt2newContext {
  private:
    int                         init_scanner();
    void                        destroy_scanner();
    char*                       buffer;
    int                         buffer_sz;
    int                         buffer_cap;
    std::unique_ptr<std::vector<CommandNode*>>   root;
  public:
    void*                       scanner;
    int                         result;
    FILE*                       is;
    char*                       ib;
    bool                        interactive;
    inline std::vector<CommandNode*> const & getRoot() { return *root; };

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

    void insertRoot(std::unique_ptr<std::vector<CommandNode*>> && n) {
        root = std::move(n);
    }

};

int yyparse(Smt2newContext*);

#endif
