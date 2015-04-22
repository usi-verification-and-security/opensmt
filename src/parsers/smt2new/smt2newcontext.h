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
#include <stdlib.h>
#include <list>

enum ASTType {
      CMD_T      , CMDL_T
    , SYM_T      , SYML_T
    , NUM_T      , NUML_T
    , SORT_T     , SORTL_T
    , SV_T       , SVL_T
    , UATTR_T    , UATTRL_T
    , PATTR_T    , PATTRL_T
    , GATTR_T    , GATTRL_T
    , SPECC_T    , SPECCL_T
    , SEXPR_T    , SEXPRL_T
    , ID_T       , IDL_T
    , LID_T      , LIDL_T
    , DEC_T      , DECL_T
    , HEX_T      , HEXL_T
    , BIN_T      , BINL_T
    , STR_T      , STRL_T
    , AS_T       , ASL_T
    , VARB_T     , VARBL_T
    , TERM_T     , TERML_T
    , QID_T      , QITL_T
    , LQID_T     , LQIDL_T
    , LET_T      , LETL_T
    , FORALL_T   , FORALLL_T
    , EXISTS_T   , EXISTSL_T
    , BANG_T     , BANGL_T
    , SSYMD_T    , SSYMDL_T
    , FSYMD_T    , FSYMDL_T
    , PFSYMD_T   , PFSYMDL_T
    , PFID_T     , PFIDL_T
    , TATTR_T    , TATTRL_T
    , TDECL_T    , TDECLL_T
    , LATTR_T    , LATTRL_T
    , LOGIC_T    , LOGICL_T
    , BOOL_T     , BOOLL_T
    , OPTION_T   , OPTIONL_T
    , INFO_T     , INFOL_T
};


class ASTNode {
  private:
    ASTType             type;
    char*               val;
    static const char*  typestr[];
  public:
    std::list< ASTNode* >*children;
    ASTNode(ASTType t, char* v) : type(t), val(v), children(NULL) {}
    ~ASTNode() {
        if (children) {
            for (std::list<ASTNode*>::const_iterator ci = children->begin(); ci != children->end(); ci++) {
                delete *ci;
            };
            delete children;
        }
//        free(val);
    }
    void                  print(std::ostream& o, int indent);
    inline const char    *typeToStr() const { return typestr[type]; }
    inline ASTType        getType()   const { return type; }
    inline const char    *getValue()  const { return val; }
};

class Smt2newContext {
  private:
    int                         init_scanner();
    void                        destroy_scanner();
    char*                       buffer;
    int                         buffer_sz;
    int                         buffer_cap;
    ASTNode*                    root;
  public:
    void*                       scanner;
    int                         result;
    FILE*                       is;
    char*                       ib;
    bool                        interactive;
    inline const ASTNode*       getRoot() { return root; };

    Smt2newContext(FILE* in) :
       buffer_sz(0)
     , buffer_cap(1)
     , root(NULL)
     , result(0)
     , is(in)
     , ib(NULL)
     , interactive(false)
    {
        init_scanner();
        buffer = (char *)malloc(buffer_cap);
    }

    Smt2newContext(char* in_s) :
       buffer_sz(0)
     , buffer_cap(1)
     , root(NULL)
     , result(0)
     , is(NULL)
     , ib(in_s)
     , interactive(true)
    {
        init_scanner();
        buffer = (char*) malloc(buffer_cap);
    }

    ~Smt2newContext() {
        destroy_scanner();
        delete root;
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

    void insertRoot(ASTNode* n) {
        root = n;
    }

    void prettyPrint(std::ostream& o) {
        o << "Starting print" << std::endl;
        root->print(o, 0);
    }
};

int smt2newparse(Smt2newContext*);

#endif
