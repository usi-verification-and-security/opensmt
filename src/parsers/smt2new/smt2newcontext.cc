/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
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


