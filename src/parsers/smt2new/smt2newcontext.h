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
#include "SMTConfig.h"

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
