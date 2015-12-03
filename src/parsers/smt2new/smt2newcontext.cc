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


#include <stdio.h>
#include "smt2newcontext.h"

void ASTNode::print(std::ostream& o, int indent) {
        for (int i = 0; i < indent; i++)
            printf(" ");
        o << "<type: " << typeToStr() << ", value: " << (val != NULL ?  val : "NULL") << ">" << std::endl;
        if (children == NULL) return;
        for (std::list<ASTNode*>::iterator i = children->begin(); i != children->end(); i++)
            (*i)->print(o, indent+1);
}

const char* ASTNode::typestr[] = {
      "command"         , "command-list"                // CMD
    , "symbol"          , "symbol-list"                 // SYM
    , "number"          , "number_list"                 // NUM
    , "sort"            , "sort-list"                   // SORT
    , "sorted-var"      , "sorted-var-list"             // SV
    , "user-attr"       , "user-attr-list"              // UATTR
    , "predef-attr"     , "predef-attr-list"            // PATTR
    , "gen-attr"        , "gen-attr-list"               // GATTR
    , "spec-const"      , "spec-const-list"             // SPECC
    , "s-expr"          , "s-expr-list"                 // SEXPR
    , "identifier"      , "identifier-list"             // ID
    , "long-identifier" , "long-identifier-list"        // LID
    , "decimal"         , "decimal-list"                // DEC
    , "hex"             , "hex-list"                    // HEX
    , "binary"          , "binary-list"                 // BIN
    , "string"          , "string-list"                 // STR
    , "as"              , "as-list"                     // AS
    , "var-binding"     , "var-binding-list"            // VARB
    , "term"            , "term-list"                   // TERM
    , "qualified-id"    , "qualified-id-list"           // QID
    , "long-qual-id"    , "long-qual-id-list"           // LQID
    , "let"             , "let-list"                    // LET
    , "forall"          , "forall-list"                 // FORALL
    , "exists"          , "exists-list"                 // EXISTS
    , "!"               , "!-list"                      // BANG
    , "sort-sym-decl"   , "sort-sym-decl-list"          // SSYMD
    , "fun-sym-decl"    , "fun-sym-decl-list"           // FSYMD
    , "par-fun-sym-decl", "par-fun-sym-decl-list"       // PFSYMD
    , "pf-2nd"          , "pf-2nd-list"                 // PFID
    , "theory-attr"     , "theory-attr-list"            // TATTR
    , "theory-decl"     , "theory-decl-list"            // TDECL
    , "logic-attr"      , "logic-attr-list"             // LATTR
    , "logic"           , "logic-list"                  // LOGIC
    , "bool"            , "bool-list"                   // BOOL
    , "option"          , "option-list"                 // OPTION
    , "info-flag"       , "info-flag-list"              // INFO
};

