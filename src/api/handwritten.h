//
// Created by Antti Hyvarinen on 29.08.22.
//

#ifndef OPENSMT_HANDWRITTEN_H
#define OPENSMT_HANDWRITTEN_H
#include <cassert>
#include <istream>
#include <string>
#include <variant>
#include <vector>

class OsmtParserException: public std::exception {
    std::string msg;
public:
    OsmtParserException(const std::string & msg) : msg(msg) {}
    virtual const char* what() const noexcept override { return msg.c_str(); }
};

struct SExpr {
    std::variant<std::string,std::vector<SExpr*>> data;
    std::string toString() const {
        if (auto str_p = std::get_if<std::string>(&data)) {
            return *str_p;
        } else if (auto vec_p = std::get_if<std::vector<SExpr*>>(&data)) {
            std::string out = "(";
            for (int i = 0; i != vec_p->size(); ++i) {
                out += (*vec_p)[i]->toString() + (i == vec_p->size()-1 ? "" : " ");
            }
            out += ")";
            return out;
        }
        assert(false);
        return {};
    }
};

class SExprParser {
    std::istream & input;
    char token = 0;
    std::vector<SExpr*> stack;
    uint32_t line = 0;
    uint32_t column = 0;

    static bool isWhiteSpace(char token) {
        return (token == ' ' or token == '\t' or token == '\r' or token == '\n');
    }

    char get() {
        auto c = static_cast<char>(input.get());
        if (c == '\n') { ++ line; column = 0; }
        ++ column;
        return c;
    }

    void advance(bool comments = true) {
        token = get();
        if (comments and token == ';') {
            while (token != '\n' and token != 0) {
                token = static_cast<char>(get());
            }
        }
    }

    void skipWhitespace() {
        while (isWhiteSpace(token)) {
            advance();
        }
    }

    std::string parseToken() {
        std::string result;
        skipWhitespace();
        bool inQuotedSymbol = token == '|';
        bool inString = token == '"';
        if (inQuotedSymbol) {
            advance(false);
        }
        while (token != 0) {
            char c = token;
            if (inQuotedSymbol and c == '|') {
                advance();
                break;
            } else if (inString and result.size() > 1 and c == '"') {
                inString = false;
            } else if (not inQuotedSymbol and not inString and (isWhiteSpace(token) or c == '(' or c == ')')) {
                break;
            }
            result.push_back(c);
            advance(not inString and not inQuotedSymbol);
        }
        return result;
    }

    void parseError(std::string const & error) {
        throw OsmtParserException("At line " + std::to_string(line) + ", column " + std::to_string(column) + ": " + error);
    }

public:
    SExprParser(std::istream & input) : input(input), token(' '), line(1) {}

    bool isEOF() {
        skipWhitespace();
        return input.eof();
    }

    SExpr * parseExpr() {
        while (not isEOF()) {
            skipWhitespace();
            if (token == '(') {
                stack.emplace_back(new SExpr{std::vector<SExpr*>()});
                advance();
                skipWhitespace();
            } else if (token == ')') {
                if (stack.empty())  {
                    parseError("Unexpected `" + std::string(1, token) + "`");
                } else if (stack.size() == 1) {
                    advance();
                    skipWhitespace();
                    break;
                } else {
                    // Copy the contents of this stack to the SExpr in the previous frame.
                    auto & prevData = std::get<std::vector<SExpr*>>((stack.rbegin()[1])->data);
                    prevData.emplace_back(stack.back());
                    assert(stack.size() > 1);
                    stack.pop_back();
                    advance();
                    skipWhitespace();
                }
            } else {
                if (stack.empty()) {
                    parseError("Expected `(` or `;`, got " + std::string(1, token));
                }
                assert(not stack.empty());
                auto & currentData = std::get<std::vector<SExpr*>>(stack.back()->data);
                currentData.emplace_back(new SExpr{parseToken()});
            }
        }
        if (stack.size() != 1) {
            parseError("Unexpected EOF");
        }
        assert(stack.size() == 1);
        auto res = stack[0];
        stack.pop_back();
        return res;
    }
};

class HandWrittenParser {
    std::istream & input;

public:
    HandWrittenParser(std::istream & input) : input(input) {}
    template<class F> void traverse(SExpr * root, F & op) {
        struct Qel { SExpr * node; uint32_t processed; };
        std::vector<Qel> queue;
        queue.emplace_back(Qel{root, static_cast<uint32_t>(0)});
        while (not queue.empty()) {
            auto & [node, processed] = queue.back();
            auto children = std::get_if<std::vector<SExpr*>>(&node->data);
            if (children and processed < children->size()) {
                ++ processed;
                queue.emplace_back(Qel{(*children)[processed-1], 0});
                continue;
            }
            assert(not children or processed == children->size());
            assert(node);
            op(*node);
            queue.pop_back();
        }
    }
    void parse() {
        SExprParser parser(input);
        class Counter {
            uint32_t count = 0;
        public:
            void operator() (SExpr &) {
                ++ count;
            }
            uint32_t getCount() const { return count; }
        };
        Counter counter;
        while (not parser.isEOF()) {
            try {
                auto sexpr = parser.parseExpr();
                traverse(sexpr, counter);
            } catch (OsmtParserException const & e) {
                std::cout << e.what() << std::endl;
                break;
            }
        }
        std::cout << std::to_string(counter.getCount()) << std::endl;
    }
};
#endif // OPENSMT_HANDWRITTEN_H