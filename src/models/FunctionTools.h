//
// Created by prova on 26.04.21.
//

#pragma once

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
public:
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

