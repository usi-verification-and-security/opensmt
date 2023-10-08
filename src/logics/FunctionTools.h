/*
 * Copyright (c) 2021-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef FUNCTION_TOOLS_H
#define FUNCTION_TOOLS_H

#include "PTRef.h"
#include "SSort.h"

class FunctionSignature {
    friend class TemplateFunction;
    SRef ret_sort;
    std::string name;
    vec<PTRef> args;
private:
    FunctionSignature() : ret_sort(SRef_Undef) {}
public:
    FunctionSignature(std::string && name, vec<PTRef> && args, SRef ret_sort)
    : ret_sort(ret_sort)
    , name(std::move(name))
    , args(std::move(args))
    {}
    std::string getName() const { return name; }
    SRef getRetSort() const { return ret_sort; }
    const vec<PTRef>& getArgs() const { return args; }
};

class TemplateFunction {
    FunctionSignature signature;
    PTRef tr_body;

    inline static constexpr std::string_view template_arg_prefix = ".arg";
    inline static std::size_t template_arg_counter = 0;
public:
    static std::string nextFreeArgumentName() { return std::string(template_arg_prefix) + std::to_string(template_arg_counter++); }

    TemplateFunction(const std::string & name, const vec<PTRef>& args_, SRef ret_sort, PTRef tr_body)
            : tr_body(tr_body)
    {
        args_.copyTo(signature.args);
        signature.name = name;
        signature.ret_sort = ret_sort;
    }
    TemplateFunction(FunctionSignature&& signature, PTRef body) : signature(std::move(signature)), tr_body(body) {}
    TemplateFunction() : tr_body(PTRef_Undef) {}
    TemplateFunction(const TemplateFunction& other) : tr_body(other.tr_body) {
        signature.ret_sort = other.getRetSort();
        signature.name = other.getName();
        other.getArgs().copyTo(signature.args);
    }
    TemplateFunction(TemplateFunction && other) = default;
    TemplateFunction& operator= (TemplateFunction &&) = default;

    std::string getName() const { return signature.getName(); }
    SRef getRetSort() const { return signature.getRetSort(); }
    PTRef getBody() const { return tr_body; }
    const vec<PTRef>& getArgs() const { return signature.getArgs(); }
    void updateBody(PTRef new_body) { tr_body = new_body; }
};

#endif // FUNCTION_TOOLS_H