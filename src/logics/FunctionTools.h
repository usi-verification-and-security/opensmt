/*
 * Copyright (c) 2021-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef FUNCTION_TOOLS_H
#define FUNCTION_TOOLS_H

#include <pterms/PTRef.h>
#include <sorts/SSort.h>

namespace opensmt {
class FunctionSignature {
public:
    FunctionSignature(std::string && name, vec<PTRef> && args, SRef ret_sort)
        : ret_sort(ret_sort),
          name(std::move(name)),
          args(std::move(args)) {}
    std::string getName() const { return name; }
    SRef getRetSort() const { return ret_sort; }
    vec<PTRef> const & getArgs() const { return args; }

private:
    friend class TemplateFunction;

    FunctionSignature() : ret_sort(SRef_Undef) {}

    SRef ret_sort;
    std::string name;
    vec<PTRef> args;
};

class TemplateFunction {
public:
    static std::string nextFreeArgumentName() {
        return std::string(template_arg_prefix) + std::to_string(template_arg_counter++);
    }

    TemplateFunction(std::string const & name, vec<PTRef> const & args_, SRef ret_sort, PTRef tr_body)
        : tr_body(tr_body) {
        args_.copyTo(signature.args);
        signature.name = name;
        signature.ret_sort = ret_sort;
    }
    TemplateFunction(FunctionSignature && signature, PTRef body) : signature(std::move(signature)), tr_body(body) {}
    TemplateFunction() : tr_body(PTRef_Undef) {}
    TemplateFunction(TemplateFunction const & other) : tr_body(other.tr_body) {
        signature.ret_sort = other.getRetSort();
        signature.name = other.getName();
        other.getArgs().copyTo(signature.args);
    }
    TemplateFunction(TemplateFunction && other) = default;
    TemplateFunction & operator=(TemplateFunction &&) = default;

    std::string getName() const { return signature.getName(); }
    SRef getRetSort() const { return signature.getRetSort(); }
    PTRef getBody() const { return tr_body; }
    vec<PTRef> const & getArgs() const { return signature.getArgs(); }
    void updateBody(PTRef new_body) { tr_body = new_body; }

private:
    inline static constexpr std::string_view template_arg_prefix = ".arg";
    inline static std::size_t template_arg_counter = 0;

    FunctionSignature signature;
    PTRef tr_body;
};
} // namespace opensmt

#endif // FUNCTION_TOOLS_H
