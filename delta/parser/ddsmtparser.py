#
# ddSMT: a delta debugger for SMT benchmarks in SMT-Lib v2 format.
# Copyright (c) 2013, Aina Niemetz
# 
# This file is part of ddSMT.
#
# ddSMT is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ddSMT is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ddSMT.  If not, see <http://www.gnu.org/licenses/>.
#

from parser.smtparser import SMTParser, SMTParseException

KIND_ANNFUN    = "<annotated fun symbol>"
KIND_FUN       = "<var or fun symbol>"
KIND_FUNAPP    = "<fun application>"
KIND_VARB      = "<var binding>"
KIND_SVAR      = "<sorted var>"

KIND_SCOPE     = "<scope>"
KIND_FESCOPE   = "<forall/exists scope>"
KIND_LSCOPE    = "<let scope>"

KIND_SORT      = "<sort>"
KIND_ARRSORT   = "<array sort>"
KIND_BVSORT    = "<bv sort>"
KIND_SORTEXPR  = "<sort expression>"

KIND_CONST     = "<const bool>"
KIND_CONSTB    = "<const bin>"
KIND_CONSTD    = "<const dec>"
KIND_CONSTN    = "<const num>"
KIND_CONSTH    = "<const hex>"
KIND_CONSTS    = "<const string>"

KIND_ANNOTN    = "!"
KIND_EXISTS    = "exists"
KIND_FORALL    = "forall"
KIND_LET       = "let"

KIND_AND       = "and"
KIND_IMPL      = "=>"
KIND_ITE       = "ite"
KIND_NOT       = "not"
KIND_OR        = "or"
KIND_XOR       = "xor"

KIND_EQ        = "="
KIND_DIST      = "distinct"
KIND_LE        = "<="
KIND_LT        = "<"
KIND_GE        = ">="
KIND_GT        = ">"

KIND_ABS       = "abs"
KIND_ADD       = "+"
KIND_DIV       = "div"
KIND_MOD       = "mod"
KIND_MUL       = "*"
KIND_NEG       = "neg"
KIND_SUB       = "-"
KIND_RDIV      = "/"

KIND_ISI       = "is_int"
KIND_TOI       = "to_int"
KIND_TOR       = "to_real"

KIND_CONC      = "concat"
KIND_EXTR      = "extract"
KIND_REP       = "repeat"
KIND_ROL       = "rotate_left"
KIND_ROR       = "rotate_right"
KIND_SEXT      = "sign_extend"
KIND_ZEXT      = "zero_extend"

KIND_BVADD     = "bvadd"
KIND_BVAND     = "bvand"
KIND_BVASHR    = "bvashr"
KIND_BVCOMP    = "bvcomp"
KIND_BVLSHR    = "bvlshr"
KIND_BVMUL     = "bvmul"
KIND_BVNAND    = "bvnand"
KIND_BVNEG     = "bvneg"
KIND_BVNOR     = "bvnor"
KIND_BVNOT     = "bvnot"
KIND_BVOR      = "bvor"
KIND_BVSDIV    = "bvsdiv"
KIND_BVSGE     = "bvsge"
KIND_BVSGT     = "bvsgt"
KIND_BVSHL     = "bvshl"
KIND_BVSLE     = "bvsle"
KIND_BVSLT     = "bvslt"
KIND_BVSMOD    = "bvsmod"
KIND_BVSREM    = "bvsrem"
KIND_BVSUB     = "bvsub"
KIND_BVUGE     = "bvuge"
KIND_BVUGT     = "bvugt"
KIND_BVUDIV    = "bvudiv"
KIND_BVULE     = "bvule"
KIND_BVULT     = "bvult"
KIND_BVUREM    = "bvurem"
KIND_BVXNOR    = "bvxnor"
KIND_BVXOR     = "bvxor"

KIND_SELECT    = "select"
KIND_STORE     = "store"

KIND_ASSERT    = "assert"
KIND_CHECKSAT  = "check-sat"
KIND_DECLFUN   = "declare-fun"
KIND_DEFFUN    = "define-fun"
KIND_DECLSORT  = "declare-sort"
KIND_DEFSORT   = "define-sort"
KIND_GETASSERT = "get-assertions"
KIND_GETASSIGN = "get-assignment"
KIND_GETPROOF  = "get-proof"
KIND_GETUCORE  = "get-unsat-core"
KIND_GETVALUE  = "get-value"
KIND_GETOPT    = "get-option"
KIND_GETINFO   = "get-info"
KIND_EXIT      = "exit"
KIND_PUSH      = "push"
KIND_POP       = "pop"
KIND_SETLOGIC  = "set-logic"
KIND_SETINFO   = "set-info"
KIND_SETOPT    = "set-option"


g_const_kinds = \
    [ KIND_CONST, KIND_CONSTB, KIND_CONSTD, KIND_CONSTN, KIND_CONSTH, 
      KIND_CONSTS ]

g_fun_kinds   = \
    [ KIND_ABS,    KIND_ADD,    KIND_AND,    KIND_BVADD,  KIND_BVAND,
      KIND_BVASHR, KIND_BVCOMP, KIND_BVLSHR, KIND_BVMUL,  KIND_BVNAND, 
      KIND_BVNEG,  KIND_BVNOR,  KIND_BVNOT,  KIND_BVOR,   KIND_BVSDIV,
      KIND_BVSGE,  KIND_BVSGT,  KIND_BVSHL,  KIND_BVSLE,  KIND_BVSLT, 
      KIND_BVSMOD, KIND_BVSREM, KIND_BVSUB,  KIND_BVUGE,  KIND_BVUGT,
      KIND_BVUDIV, KIND_BVULE,  KIND_BVULT,  KIND_BVUREM, KIND_BVXNOR, 
      KIND_BVXOR,  KIND_CONC,   KIND_DIST,   KIND_DIV,    KIND_EQ,
      KIND_EXTR,   KIND_GE,     KIND_GT,     KIND_IMPL,   KIND_ISI,
      KIND_ITE,    KIND_LE,     KIND_LT,     KIND_MOD,    KIND_MUL,
      KIND_NEG,    KIND_NOT,    KIND_OR,     KIND_RDIV,   KIND_REP,
      KIND_ROL,    KIND_ROR,    KIND_SELECT, KIND_SEXT,   KIND_STORE,
      KIND_SUB,    KIND_TOI,    KIND_TOR,    KIND_XOR,    KIND_ZEXT]

g_cmd_kinds   = \
    [ KIND_ASSERT,   KIND_CHECKSAT, KIND_DECLFUN,   KIND_DEFFUN, 
      KIND_DECLSORT, KIND_DEFSORT,  KIND_GETASSERT, KIND_GETASSIGN, 
      KIND_GETPROOF, KIND_GETUCORE, KIND_GETVALUE,  KIND_GETOPT,
      KIND_GETINFO,  KIND_EXIT,     KIND_PUSH,      KIND_POP,
      KIND_SETLOGIC, KIND_SETINFO,  KIND_SETOPT ]



class DDSMTParseCheckException (Exception):

    def __init__ (self, msg):
        self.msg = msg
    
    def __str__ (self):
        return "[ddsmt] Error: {}".format(self.msg)


class DDSMTParseException (SMTParseException):

    def __str__ (self):
        return "[ddsmt] {}:{}:{}: {}".format(
                self.filename, self.line, self.col, self.msg)


class SMTNode:

    g_id = 0
    g_smtformula = None

    def __init__ (self, kind = "none", sort = None, children = []):
        assert (isinstance (children, list))
        SMTNode.g_id += 1
        self.id = SMTNode.g_id
        self.kind = kind
        self.sort = sort
        self.children = children

    def __str__ (self):
        return str(self.get_subst()) if self.is_subst() else \
                "({}{})".format(self.kind, self.children2str())

    def children2str(self):
        return " " + " ".join([str(c) for c in self.children]) \
                            if self.children else ""

    def dump (self, outfile, lead = " "):
        if self.is_subst():
            self.get_subst().dump(outfile, lead)
        else:
            outfile.write(lead)
            outfile.write(str(self))

    def is_const (self):
        return False

    def is_fun (self):
        return False

    def is_write (self):
        return False

    def is_read (self):
        return False

    def is_ite (self):
        return False

    def is_let (self):
        return False

    def subst (self, substitution):
        SMTNode.g_smtformula.subst(self, substitution)

    def get_subst (self):
        return self if not self.is_subst() else \
                SMTNode.g_smtformula.get_subst(self)

    def is_subst (self):
        return SMTNode.g_smtformula and SMTNode.g_smtformula.is_subst(self)


class SMTSortNode (SMTNode):

    def __init__ (self, name, nparams = 0, kind = KIND_SORT):
        super().__init__(kind)
        self.name = name
        self.nparams = nparams
    
    def __str__ (self):
        return self.name

    def is_bv_sort (self):
        return False

    def is_arr_sort (self):
        return False


class SMTArraySortNode (SMTSortNode):

    def __init__ (self, index_sort = None, elem_sort = None):
        super().__init__(
                SMTArraySortNode.name(index_sort, elem_sort), 2, KIND_ARRSORT)
        self.index_sort = index_sort
        self.elem_sort = elem_sort

    @staticmethod
    def name (index_sort, elem_sort):
        assert (index_sort != None or elem_sort == None)
        return "Array" if index_sort == None and elem_sort == None \
                       else "(Array {!s} {!s})".format(index_sort, elem_sort)

    def is_arr_sort (self):
        return True


class SMTBVSortNode (SMTSortNode):

    def __init__ (self, bw):
        super().__init__(SMTBVSortNode.name(bw), 0, KIND_BVSORT)
        self.bw = bw

    @staticmethod
    def name (bw):
        return "(_ BitVec {})".format(bw)

    def is_bv_sort (self):
        return True


class SMTSortExprNode (SMTNode):

    def __init__ (self, sort, symbols = []):
        super().__init__(KIND_SORTEXPR, sort)
        self.symbols = symbols  # arg symbols
        
    def __str__ (self):
        if self.is_subst():
            return str(self.get_subst())
        return str(self.sort) \
                if self.sort.nparams == 0 else "({!s} {})".format(
                        self.sort, " ".join([str(s) for s in self.symbols]))


class SMTConstNode (SMTNode):

    def __init__ (self, kind, sort, value = 0):
        assert (kind in g_const_kinds)
        super().__init__(kind, sort)
        self.value = value

    def __str__ (self):
        if self.is_subst():
            return str(self.get_subst())
        return str(self.value)

    def is_const (self):
        return True


class SMTBVConstNode (SMTConstNode):

    def __str__ (self):
        assert (self.kind != KIND_CONST)
        if self.is_subst():
            return str(self.get_subst())
        if self.kind == KIND_CONSTH:
            shex = str(hex(self.value)[2:])
            nzeros = self.sort.bw // 4 - len(shex)
            return "#x{}{}".format(
                    "".join(['0' for i in range(0, nzeros)]), shex)
        elif self.kind == KIND_CONSTB:
            sbin = str(bin(self.value)[2:])
            nzeros = self.sort.bw - len(sbin)
            return "#b{}{}".format(
                    "".join(['0' for i in range(0, nzeros)]), sbin)
        assert (self.kind == KIND_CONSTN)
        return "(_ bv{} {})".format(self.value, self.sort.bw)


class SMTFunNode (SMTNode):

    def __init__ (self, name, sort, sorts = [], indices = []):
        assert (isinstance (sorts, list))
        assert (isinstance (indices, list))
        super().__init__(KIND_FUN, sort)
        self.name = name
        self.sorts = sorts      # signature sorts
        self.indices = [int(s.value) for s in indices]

    def __str__ (self):
        if self.is_subst():
            return str(self.get_subst())
        if self.indices == []:
            return self.name
        return "(_ {} {})".format(
                self.name, " ".join([str(s) for s in self.indices]))

    def is_fun (self):
        return True


class SMTAnFunNode (SMTNode):

    def __init__ (self, fun, sort):
        super().__init__(KIND_ANNFUN, sort)
        self.fun = fun

    def __sizeof (self):
        return super().__sizeof__() + self.fun.__sizeof__()

    def __str__ (self):
        return str(self.get_subst()) if self.is_subst() else \
                "(as {!s} {!s})".format(self.fun, self.sort)


class SMTFunAppNode (SMTNode):        
         
    def __init__ (self, fun, kind, sort, children):
        assert (isinstance(fun, SMTFunNode))
        assert (len(children) >= 1)
        super().__init__(kind, sort, children)
        self.fun = fun

    def __str__ (self):
        # we have to prevent recursive calls here, else deep nesting levels
        # blow up the recursion depth limit
        strings = []
        to_visit = [self]
        visited = {}
        while to_visit:
            cur = to_visit.pop().get_subst()
            if type(cur) != SMTFunAppNode:
                strings.append(str(cur))
            else:
                if cur.id not in visited:
                    to_visit.append(cur)
                    to_visit.extend(cur.children)
                    visited[cur.id] = cur.id
                else:
                    cs = []
                    for c in cur.children:
                        cs.append(strings.pop())
                    strings.append(
                            "({} {})".format(
                                cur.fun, 
                                " ".join([s for s in cs])))
        assert (len(strings) == 1)
        return strings.pop()

    def dump (self, outfile, lead = " "):
        # we have to prevent recursive calls here, else deep nesting levels
        # blow up the recursion depth limit
        to_visit = [self]
        visited = {}
        while to_visit:
            cur = to_visit.pop().get_subst()
            if type(cur) != SMTFunAppNode:
                cur.dump(outfile)
            else:
                if cur.id not in visited:
                    to_visit.append(cur)
                    outfile.write(lead)
                    outfile.write("({}".format(cur.fun))
                    to_visit.extend(cur.children[::-1])
                    visited[cur.id] = cur.id
                else:
                    outfile.write(")")

    def is_write (self):
        return self.kind == KIND_STORE

    def is_read (self):
        return self.kind == KIND_SELECT

    def is_ite (self):
        return self.kind == KIND_ITE


class SMTVarBindNode (SMTNode):

    def __init__ (self, var, children):
        assert (isinstance (var, SMTFunNode))
        assert (isinstance (children, list))
        assert (len(children) == 1)
        super().__init__(KIND_VARB, None, children)
        self.var = var

    def __str__ (self):
        assert (len(self.children) == 1)
        return str(self.get_subst()) if self.is_subst() else \
                "({} {!s})".format(self.var.name, self.children[0])

    def dump (self, outfile, lead = " " ):
        if self.is_subst():
            self.get_subst().dump(outfile, lead)
        else:
            outfile.write(lead)
            outfile.write("({}".format(self.var.name))
            self.children[0].dump(outfile)
            outfile.write(")")


class SMTSortedQVarNode (SMTNode):
    
    def __init__ (self, var):
        assert (isinstance (var, SMTFunNode))
        assert (var.sort)
        super().__init__(KIND_SVAR, var.sort)
        self.var = var
        
    def __str__ (self):
        return str(self.var)


class SMTForallExistsNode (SMTNode):

    def __init__ (self, svars, kind, children):
        assert (kind in (KIND_FORALL, KIND_EXISTS))
        assert (len(children) == 1)
        super().__init__(kind, children[0].sort, children)
        self.svars = svars

    def __str__ (self):
        # we have to prevent recursive calls here, else deep nesting levels
        # blow up the recursion depth limit
        strings = []
        to_visit = [self]
        visited = {}
        while to_visit:
            cur = to_visit.pop().get_subst()
            if type(cur) != SMTForallExistsNode:
                strings.append(str(cur))
            else:
                if cur.id not in visited:
                    to_visit.append(cur)
                    to_visit.extend(cur.children)
                    visited[cur.id] = cur.id
                else:
                    assert (len(strings) == 1)
                    strings.append(
                            "({} ({}) {})".format(
                                cur.kind, 
                                " ".join(
                                    ["({} {!s})".format(s.var.name, s.var.sort)
                                    for s in cur.svars]) \
                                            if len(cur.svars) > 0 else "",
                                strings.pop()))
        assert (len(strings) == 1)
        return strings.pop()

    def dump (self, outfile, lead = " "):
        # we have to prevent recursive calls here, else deep nesting levels
        # blow up the recursion depth limit
        to_visit = [self]
        visited = {}
        while to_visit:
            cur = to_visit.pop().get_subst()
            if type(cur) != SMTForallExistsNode:
                cur.dump(outfile)
            else:
                if cur.id not in visited:
                    to_visit.append(cur)
                    outfile.write(lead)
                    outfile.write("({} ({})".format(
                        cur.kind,
                        " ".join(["({} {!s})".format(s.var.name, s.var.sort)
                            for s in cur.svars]) if len(cur.svars) > 0 else ""))
                    to_visit.extend(cur.children[::-1])
                    visited[cur.id] = cur.id
                else:
                    outfile.write(")")


class SMTLetNode (SMTNode):

    def __init__ (self, children):
        super().__init__(KIND_LET, children[-1].sort, children)

    def __str__ (self):
        # we have to prevent recursive calls here, else deep nesting levels
        # blow up the recursion depth limit
        strings = []
        to_visit = [self]
        visited = {}
        while to_visit:
            cur = to_visit.pop().get_subst()
            if type(cur) != SMTLetNode:
                strings.append(str(cur))
            else:
                if cur.id not in visited:
                    to_visit.append(cur)
                    to_visit.extend(cur.children)
                    visited[cur.id] = cur.id
                else:
                    cs = []
                    for c in cur.children:
                        cs.append(strings.pop())
                    strings.append(
                            "({} ({}) {})".format(
                                cur.kind, 
                                " ".join([s for s in cs[0:-1]]),
                                cs[-1]))
        assert (len(strings) == 1)
        return strings.pop()

    def dump (self, outfile, lead = " "):
        # we have to prevent recursive calls here, else deep nesting levels
        # blow up the recursion depth limit
        to_visit = [self]
        visited = {}
        cntvb = 0
        while to_visit:
            cur = to_visit.pop().get_subst()
            if type(cur) != SMTLetNode:
                if type(cur) != SMTVarBindNode:
                    outfile.write(")")
                    cur.dump(outfile)
                    cntvb = 0
                else:
                    if cntvb:
                        cur.dump(outfile)
                    else:
                        cur.dump(outfile, "")
                    cntvb += 1
            else:
                if cntvb:
                    outfile.write(")")
                    cntvb = 0
                if cur.id not in visited:
                    to_visit.append(cur)
                    outfile.write(lead)
                    outfile.write("({} (".format(cur.kind))
                    to_visit.extend(cur.children[::-1])
                    visited[cur.id] = cur.id
                else:
                    outfile.write(")")

    def is_let (self):
        return True


class SMTAnnNode (SMTNode):

    def __init__ (self, attributes, sort, children, name = None):
        assert (len(children) == 1)
        super().__init__(KIND_ANNOTN, sort, children)
        self.attributes = attributes
        # we need to treat annotation nodes as function nodes in case that 
        # attribute ':named' is given
        self.name = name
        self.indices = []
        # we need to distinguish full dumps and name-only dumps for named 
        # annotation nodes
        self.dumped = False 
    def __str__ (self):
        return str(self.get_subst()) if self.is_subst() else \
                "(! {!s} {})".format(
                        self.children[0], 
                        " ".join([str(a) for a in self.attributes]))

    def dump (self, outfile, lead = " "):
        if self.is_subst():
            self.get_subst().dump(outfile, lead)
        else:
            outfile.write(lead)
            if self.dumped:  # name-only
                outfile.write(self.name)
            else:            # full dump
                outfile.write(str(self))
                self.dumped = True


class SMTCmdNode:         

    g_id = 0
    g_smtformula = None

    def __init__ (self, kind, children = []):
        global g_cmd_kinds
        assert (isinstance (children, list))
        assert (kind in g_cmd_kinds)
        SMTCmdNode.g_id += 1
        self.id = SMTCmdNode.g_id
        self.kind = kind
        self.children = children

    def __str__ (self):
        if self.is_subst():
            return ""
        if self.kind == KIND_DECLFUN:
            assert (len(self.children) == 1)
            assert (isinstance(self.children[0], SMTFunNode))
            fun = self.children[0]
            return "({} {} ({}) {})".format(
                    self.kind, 
                    fun.name,
                    " ".join([str(s) for s in fun.sorts]) \
                            if len(fun.sorts) > 0 else "",
                    str(fun.sort))
        elif self.kind == KIND_DEFFUN:
            assert (len(self.children) == 3)
            assert (isinstance(self.children[0], SMTFunNode))
            fun = self.children[0]
            svars = self.children[1]
            fterm = self.children[2]
            return "({} {} ({}) {!s} {!s})".format(
                    self.kind,
                    fun.name,
                    " ".join(["({} {!s})".format(s.name, s.sort) 
                              for s in svars]) if len(svars) > 0 else "",
                    fun.sort,
                    fterm)
        elif self.kind == KIND_DECLSORT:
            assert (len(self.children) == 1)
            assert (isinstance(self.children[0], SMTSortNode))
            sort = self.children[0]
            return "({} {} {})".format(
                    self.kind, sort.name, sort.nparams)
        elif self.kind == KIND_DEFSORT:
            assert (len(self.children) == 3)
            assert (isinstance(self.children[0], SMTSortNode))
        return "({}{})".format(self.kind, self.children2str())

    def dump (self, outfile, lead = ""):
        if self.is_subst():
            return
        outfile.write(lead)
        if self.kind == KIND_DECLFUN:
            assert (len(self.children) == 1)
            assert (isinstance(self.children[0], SMTFunNode))
            fun = self.children[0]
            outfile.write("({} {} ({}) {})\n".format(
                    self.kind, 
                    fun.name,
                    " ".join([str(s) for s in fun.sorts]) \
                            if len(fun.sorts) > 0 else "",
                    str(fun.sort)))
        elif self.kind == KIND_DEFFUN:
            assert (len(self.children) == 3)
            assert (isinstance(self.children[0], SMTFunNode))
            fun = self.children[0]
            svars = self.children[1]
            fterm = self.children[2]
            outfile.write("({} {} ({}) {!s} {!s})\n".format(
                    self.kind,
                    fun.name,
                    " ".join(["({} {!s})".format(s.name, s.sort) 
                              for s in svars]) if len(svars) > 0 else "",
                    fun.sort,
                    fterm))
        elif self.kind == KIND_DECLSORT:
            assert (len(self.children) == 1)
            assert (isinstance(self.children[0], SMTSortNode))
            sort = self.children[0]
            outfile.write("({} {} {})\n".format(
                    self.kind, sort.name, sort.nparams))
        elif self.kind == KIND_ASSERT:
            outfile.write("({}".format(self.kind))
            assert (len(self.children) == 1)
            self.children[0].dump(outfile)
            outfile.write(")\n")
        else:
            if self.kind == KIND_DEFSORT:
                assert (len(self.children) == 3)
                assert (isinstance(self.children[0], SMTSortNode))
            outfile.write("{!s}".format(self))
            if self.kind != KIND_EXIT:
                outfile.write("\n")

    def children2str (self):
        res = [""]
        for c in self.children:
            if isinstance (c, list):
                res.append("({})".format(
                    " ".join([str(cc) for cc in c])))
            else:
                res.append(str(c))
        return " ".join([s for s in res]) if self.children else ""

    def is_assert (self):
        return self.kind == KIND_ASSERT
    
    def is_setlogic (self):
        return self.kind == KIND_SETLOGIC

    def is_exit (self):
        return self.kind == KIND_EXIT

    def subst (self, substitution):
        SMTCmdNode.g_smtformula.subst(self, substitution)

    def get_subst (self):
        return self if not self.is_subst() else \
                SMTCmdNode.g_smtformula.get_subst(self)

    def is_subst (self):
        return SMTCmdNode.g_smtformula and \
                SMTCmdNode.g_smtformula.is_subst(self)


class SMTPushCmdNode (SMTCmdNode):

    def __init__ (self, nscopes, scope = None):
        assert (nscopes > 0)
        super().__init__(KIND_PUSH)
        self.nscopes = nscopes
        self.scope = scope
        # Note: self.scope is the scope directly associated with this push
        #       i.e. for e.g. push 2, 2 scopes are opened and the first one
        #       is the  one associated with the resp. push command
        
    def __str__ (self):
        return "" if self.is_subst() else \
                "({} {})".format(self.kind, self.nscopes)


class SMTPopCmdNode (SMTCmdNode):

    def __init__ (self, nscopes):
        assert (nscopes > 0)
        super().__init__(KIND_POP)
        self.nscopes = nscopes

    def __str__ (self):
        return "" if self.is_subst() else \
                "({} {})".format(self.kind, self.nscopes)



class SMTScopeNode:

    g_id = 0
    g_smtformula = None

    def __init__ (self, level = 0, prev = None, kind = KIND_SCOPE):
        assert (kind in (KIND_SCOPE, KIND_FESCOPE, KIND_LSCOPE))
        SMTScopeNode.g_id += 1
        self.id = SMTScopeNode.g_id
        self.level  = level
        self.prev   = prev
        self.kind   = kind
        self.scopes = []
        self.cmds   = []
        self.funs   = {}
        self.sorts  = {}
        self.declfun_cmds = {}  # used for substition with fresh variables

    def __str__ (self):
        if self.is_subst():
            return ""
        res = []
        for cmd in self.cmds:
            if cmd.kind == KIND_SETLOGIC:
                res.append(str(cmd))
                # dump declarations of substition variables
                for name in self.declfun_cmds:
                    res.append(str(self.declfun_cmds[name]))
            elif cmd.kind == KIND_PUSH:
                assert (len(self.scopes) > 0)
                assert (cmd.scope in self.scopes)
                assert (cmd.scope.is_regular())
                if cmd.scope.is_subst():
                    continue
                res.append(str(cmd))
                res.append(str(cmd.scope))
            else:
                res.append(str(cmd))
        return "\n".join([s for s in res if s != ""])

    def dump (self, outfile, lead = ""):
        if self.is_subst():
            return
        outfile.write(lead)
        for cmd in self.cmds:
            if cmd.kind == KIND_SETLOGIC:
                cmd.dump(outfile)
                # dump declarations of substition variables
                for name in self.declfun_cmds:
                    self.declfun_cmds[name].dump(outfile)
            elif cmd.kind == KIND_PUSH:
                assert (len(self.scopes) > 0)
                assert (cmd.scope in self.scopes)
                assert (cmd.scope.is_regular())
                if cmd.scope.is_subst():
                    continue
                cmd.dump(outfile)
                cmd.scope.dump(outfile)
            else:
                cmd.dump(outfile)
        
    def is_regular (self):
        return self.kind == KIND_SCOPE

    def subst (self, substitution):
        SMTScopeNode.g_smtformula.subst(self, substitution)

    def get_subst (self):
        return self if not self.is_subst() else \
                SMTScopeNode.g_smtformula.get_subst(self)

    def is_subst (self):
        return SMTScopeNode.g_smtformula and \
                SMTScopeNode.g_smtformula.is_subst(self)

    def is_substvar (self, node):
        if not node.is_fun():
            return False
        return node.name in self.declfun_cmds



class SMTSubstList:
    def __init__ (self):
        self.substs = {}

    def subst (self, node, substitution):
        assert (not substitution or \
                not substitution.is_subst() or \
                not substitution.get_subst().is_subst())
        self.substs[node.id] = substitution \
                if not substitution else substitution.get_subst()

    def is_subst (self, node):
        return node.id in self.substs

    def get_subst (self, node):
        while node.is_subst():
            node = self.substs[node.id]
        return node


class SMTNodeSubstList (SMTSubstList):

    def subst (self, node, substitution):
        assert (isinstance (node, SMTNode))
        super().subst(node, substitution)


class SMTScopeSubstList (SMTSubstList):

    def subst (self, node, substitution):
        assert (isinstance (node, SMTScopeNode))
        assert (not self.is_subst(node))
        super().subst(node, substitution)


class SMTCmdSubstList (SMTSubstList):

    def subst (self, node, substitution):
        assert (isinstance (node, SMTCmdNode))
        assert (not self.is_subst(node))
        super().subst(node, substitution)


class SMTFormula:

    def __init__ (self):
        self.logic = "none"
        self.scopes = SMTScopeNode ()
        self.cur_scope = self.scopes
        self.subst_scopes = SMTScopeSubstList ()
        self.subst_cmds = SMTCmdSubstList ()
        self.subst_nodes = SMTNodeSubstList ()
        self.scopes_cache = {  # currently visible scopes 
                self.scopes.id : self.scopes } 
        self.funs_cache = {}   # fun name -> declaring scopes
        self.anns_cache = []   # named annotation nodes
        self.__add_predefined_sorts ()

    def __add_predefined_sorts (self):
        self.add_sort ("Bool")
        self.add_sort ("Int")
        self.add_sort ("Real")
        self.add_sort ("String")
        self.add_arrSort ()      # abstract array base sort

    def dump (self, filename = None, root = None):
        out = root if root != None else self.scopes
        for ann in self.anns_cache:
            ann.dumped = False  # reset 
        if not filename:
            out.dump(sys.stdout)    
            sys.stdout.write("\n")
        else:
            with open(filename, 'w') as outfile:
                out.dump(outfile)
                outfile.write("\n")

    def is_bv_logic (self):
        return self.logic.find("BV") >= 0

    def is_int_logic (self):
        return self.logic.find("I") >= 0

    def is_real_logic (self):
        return self.logic.find("R") >= 0

    def is_arr_logic (self):
        return self.logic in ("AUFLIA", "AUFLIRA", "AUFNIRA", "QF_ABV", 
                              "QF_AUFBV", "QF_AUFLIA", "QF_AX")

    def is_substvar (self, node):
        return self.scopes.is_substvar(node)

    def subst (self, node, substitution):
        if isinstance (node, SMTScopeNode):
            self.subst_scopes.subst(node, substitution)
        elif isinstance (node, SMTCmdNode):
            self.subst_cmds.subst(node, substitution)
        else:
            assert (isinstance (node, SMTNode))
            self.subst_nodes.subst(node, substitution)
            if node.is_fun() and self.is_substvar(node):
                del (self.scopes.declfun_cmds[node.name])


    def is_subst (self, node):
        if isinstance (node, SMTScopeNode):
            return self.subst_scopes.is_subst(node)
        elif isinstance (node, SMTCmdNode):
            return self.subst_cmds.is_subst(node)
        assert (isinstance (node, SMTNode))
        return self.subst_nodes.is_subst(node)

    def get_subst (self, node):
        if isinstance (node, SMTScopeNode):
            assert (not self.subst_scopes.is_subst(node) or 
                        self.subst_scopes.get_subst(node) == None)
            return self.subst_scopes.get_subst(node)
        elif isinstance (node, SMTCmdNode):
            assert (not self.subst_cmds.is_subst(node) or 
                    self.subst_cmds.get_subst(node) == None)
            return self.subst_cmds.get_subst(node)
        assert (isinstance (node, SMTNode))
        assert (self.subst_nodes.get_subst(node))
        return self.subst_nodes.get_subst(node)

    def open_scope (self, nscopes = 1, kind = KIND_SCOPE):
        assert (kind == KIND_SCOPE or nscopes == 1) 
        # Note: forall, exists open exactly one scope
        first_scope = None
        for i in range (nscopes):
            new_scope = SMTScopeNode (
                    self.cur_scope.level + 1, self.cur_scope, kind)
            if not first_scope:
                first_scope = new_scope
            self.cur_scope.scopes.append(new_scope)
            self.cur_scope = new_scope
            self.scopes_cache[self.cur_scope.id] = self.cur_scope
        return first_scope  # scope associated with parent push cmd

    def close_scope (self, nscopes = 1):
        for i in range (nscopes):
            assert (self.cur_scope.prev != None)
            del(self.scopes_cache[self.cur_scope.id])
            self.cur_scope = self.cur_scope.prev

    def constNode (self, kind, sort, value):
        assert (kind in (KIND_CONST, KIND_CONSTN, KIND_CONSTD, KIND_CONSTS))
        return SMTConstNode (kind, sort, value)

    def zeroConstNode (self,  kind):
        assert (kind in (KIND_CONSTN, KIND_CONSTD))
        return self.constNode (KIND_CONSTN, self.sortNode("Int"), 0) \
                if kind == KIND_CONSTN \
                else self.constNode (KIND_CONSTD, self.sortNode("Real"), 0.0)

    def zeroConstNNode (self):
        return self.zeroConstNode (KIND_CONSTN)

    def zeroConstDNode (self):
        return self.zeroConstNode (KIND_CONSTD)

    def boolConstNode (self, value):
        assert (value in ("true", "false"))
        return SMTConstNode (KIND_CONST, self.sortNode ("Bool"), value)

    def bvConstNode (self, kind, bw, value):
        assert (isinstance (bw, int))
        return SMTBVConstNode (kind, self.bvSortNode(bw), value)

    def bvZeroConstNode (self, sort):
        assert (sort.is_bv_sort())
        return self.bvConstNode (KIND_CONSTN, sort.bw, 0)

    def find_sort_and_scope (self, name, scope = None):
        scope = scope if scope else self.cur_scope
        while scope:
            if name in scope.sorts:
                assert (isinstance (scope.sorts[name], SMTSortNode))
                return (scope.sorts[name], scope)
            scope = scope.prev
        return None
        
    def find_sort (self, name, scope = None):
        scope = scope if scope else self.cur_scope
        res = self.find_sort_and_scope (name, scope)
        return res[0] if res else None
    
    def delete_sort (self, name, scope = None):
        scope = scope if scope else self.cur_scope
        assert (self.find_sort (name, scope))
        while scope:
            if name in scope.sorts:
                assert (isinstance (scope.sorts[name], SMTSortNode))
                del scope.sorts[name]
                assert (not self.find_sort (name, scope))
                return
            scope = scope.prev

    def add_sort (self, name, nparams = 0, scope = None):
        scope = scope if scope else self.scopes  # default: level 0
        assert (not self.find_sort (name, self.cur_scope))
        scope.sorts[name] = SMTSortNode (name, nparams)
        return scope.sorts[name]

    def add_bvSort (self, bw):
        name = SMTBVSortNode.name(bw)
        assert (not self.find_sort(name, self.scopes))
        self.scopes.sorts[name] = SMTBVSortNode (bw)  # level 0
        return self.scopes.sorts[name]

    def add_arrSort (self, index_sort = None, elem_sort = None, scope = None):
        scope = scope if scope else self.scopes  # default: level 0
        name = SMTArraySortNode.name(index_sort, elem_sort)
        assert (not self.find_sort(name, scope))
        scope.sorts[name] = SMTArraySortNode (index_sort, elem_sort)
        return scope.sorts[name]

    def sortNode (self, name, nparams = 0, scope = None, new = False):
        scope = scope if scope else self.scopes  # default: level 0
        sort = self.find_sort (name, scope)      # concrete sort already added?
        if not sort:
            if nparams > 0:
                # abstract sort already declared?
                res = self.find_sort_and_scope (name[1:-1].split()[0], scope)
                
                if res:
                    if res[0].nparams != nparams:
                        if not new:
                            raise DDSMTParseCheckException (
                                    "'{} expects {} parameters".format(
                                        name, nparams))
                        else:
                            raise DDSMTParseCheckException (
                                    "previous declaration of '{}' with " \
                                    "{} was here".format(name, res[0].nparams))
                        sort = res[0]
                        scope = res[1]
                        if sort.is_arr_sort():
                            assert (sort.nparams == nparams)
                            name = name[1:-1].split()
                            assert (name[0] == "Array")
                            assert (len(name) == 3)
                            return self.add_arrSort (name[1], name[2], scope)
            elif not new:
                raise DDSMTParseCheckException (
                        "sort '{}' undeclared".format(name))
            return self.add_sort (name, nparams, scope)
        return sort

    def bvSortNode (self, bw):
        name = SMTBVSortNode.name(bw)
        sort = self.find_sort(name, self.scopes)  # level 0
        if not sort:
            sort = self.add_bvSort(bw)
        return sort

    def arrSortNode (self, index_sort = None, elem_sort = None, scope = None):
        scope = scope if scope else self.scopes  # default: level 0
        name = SMTArraySortNode.name(index_sort, elem_sort)
        sort = self.find_sort(name, scope)
        if not sort:
            return self.add_arrSort (index_sort, elem_sort, scope)
        return sort

    def find_fun (self, name, indices = [], scope = None, find_nested = True):
        global g_fun_kinds
        # level 0 shortcut
        if name in g_fun_kinds:  # default at level 0
            if name in self.scopes.funs \
               and self.scopes.funs[name].indices == indices:
                   return self.scopes.funs[name]
            else:
                return None
        # check given / current scope first
        scope = scope if scope else self.cur_scope
        assert (scope.id in self.scopes_cache)
        if name in scope.funs and scope.funs[name].indices == indices:
            return scope.funs[name]
        # check outer scopes
        if find_nested and name in self.funs_cache:
            scopes = self.funs_cache[name]
            for s in reversed(scopes):
                if s.id > scope.id:
                    continue
                if s.id in self.scopes_cache:
                    assert (name in s.funs)
                    if s.funs[name].indices == indices:
                        return s.funs[name]
        return None

    def add_fun (self, name, sort, sorts, indices, scope = None):
        scope = scope if scope else self.scopes
        scope.funs[name] = SMTFunNode (name, sort, sorts, indices)
        if name in self.funs_cache:
            self.funs_cache[name].append(scope)
        else:
            self.funs_cache[name] = [scope]
        return scope.funs[name]

    def delete_fun (self, name, indices = [], scope = None):
        global g_fun_kinds
        # level 0 shortcut
        if name in g_fun_kinds:  # default at level 0
            if name in self.scopes.funs \
               and self.scopes.funs[name].indices == indices:
                   del(self.scopes.funs[name])
            return
        # check given / current scope first
        scope = scope if scope else self.cur_scope
        if name in scope.funs:
            del(scope.funs[name])
        # check outer scopes
        elif name in self.funs_cache:
            scopes = self.funs_cache[name]
            for s in reversed(scopes):
                if s.id > scope.id:
                    continue
                if s.id in self.scopes_cache:
                    assert (name in s.funs)
                    if s.funs[name].indices == indices:
                        del(s.funs[name])

    def funNode (self, name, sort, sorts = [], indices = [], scope = None,
                 find_nested = True):
        global fun_kinds
        scope = scope if scope and name not in g_fun_kinds \
                      else self.scopes  # default: level 0
        fun = self.find_fun (name, indices, scope, find_nested)
        if not fun:
            return self.add_fun (name, sort, sorts, indices, scope)
        return fun

    def anFunNode (self, name, sort, indices = []):
        if name in g_fun_kinds:
            fun = self.funNode (name, None, [], indices)
        else:
            fun = self.find_fun (name, indices)
            if not fun:
                raise DDSMTParseCheckException (
                        "function '{}' undeclared".format(name))
        return SMTAnFunNode (fun, sort)

    def check_funApp (self, fun, kind, children):
        sortbool = self.sortNode("Bool")
        sortint = self.sortNode("Int")
        sortreal = self.sortNode("Real")
        # args declaration check
        for c in children:
            if not c.sort:
                assert (c.kind == KIND_FUN)
                raise DDSMTParseCheckException (
                        "function '{!s}' undeclared".format(c))
        # number of args check
        if ((len(children) != 1 and 
                 kind in (KIND_ABS, KIND_BVNEG, KIND_BVNOT, KIND_EXTR, KIND_ISI,
                          KIND_NOT, KIND_NEG,   KIND_TOI,   KIND_TOR,  KIND_REP,
                          KIND_ROL, KIND_ROR,   KIND_SEXT,  KIND_ZEXT)) or
            (len(children) != 2 and
                 kind in (KIND_BVADD,  KIND_BVAND,  KIND_BVASHR, KIND_BVCOMP, 
                          KIND_BVLSHR, KIND_BVMUL,  KIND_BVNAND, KIND_BVNOR,
                          KIND_BVOR,   KIND_BVSDIV, KIND_BVSGE,  KIND_BVSGT,
                          KIND_BVSHL,  KIND_BVSLE,  KIND_BVSLT,  KIND_BVSMOD,
                          KIND_BVSREM, KIND_BVSUB,  KIND_BVUGE,  KIND_BVUGT,
                          KIND_BVUDIV, KIND_BVULE,  KIND_BVULT,  KIND_BVUREM,
                          KIND_BVXNOR, KIND_BVXOR,  KIND_CONC,   KIND_MOD,
                          KIND_SELECT)) or
            (len(children) != 3 and 
                kind in (KIND_ITE, KIND_STORE))):
            raise DDSMTParseCheckException (
                    "invalid number of arguments to '{!s}': {}" \
                    "".format(fun, len(children)))
        # number of indices check
        if self.is_bv_logic:
            if kind == KIND_EXTR and len(fun.indices) != 2:
                raise DDSMTParseCheckException (
                    "'{!s}' expects exactly two indices, {} given" \
                    "".format(fun.name, len(fun.indices)))
            elif kind in (KIND_REP, KIND_ROL, KIND_ROR, KIND_SEXT, KIND_ZEXT) \
                 and len(fun.indices) != 1:
                raise DDSMTParseCheckException (
                    "'{!s}' expects exactly one index, {} given" \
                    "".format(fun.name, len(fun.indices)))
        # args sort Bool check
        if kind in (KIND_AND, KIND_IMPL, KIND_NOT, KIND_OR, KIND_XOR):
            for c in children:
                if not c.sort == sortbool:
                    raise DDSMTParseCheckException (
                        "'{!s}' expects sort 'Bool' as argument(s), " \
                        "found '{}'".format(fun, c.sort))
        # args Int check
        elif kind in (KIND_ABS, KIND_DIV, KIND_MOD, KIND_TOR):
            for c in children:
                if not c.sort == sortint:
                    raise DDSMTParseCheckException (
                        "'{!s}' expects sort 'Int' as argument(s), " \
                        "found '{}'".format(fun, c.sort))
        # args Real check
        elif kind in (KIND_RDIV, KIND_ISI, KIND_TOI):
            for c in children:
                if c.sort not in (sortint, sortreal):
                    raise DDSMTParseCheckException (
                        "'{!s}' expects sort 'Real' as argument(s)" \
                        "".format(fun))
        # args Int or Real check
        elif kind in (KIND_ADD, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_MUL, 
                      KIND_NEG, KIND_SUB):
            c0 = children[0]
            if c0.sort not in (sortint, sortreal):
                raise DDSMTParseCheckException (
                    "'{!s}' expects sort 'Int' or 'Real' as argument(s)" \
                    "".format(fun))
        # args BV sort check
        elif kind in (KIND_CONC, KIND_EXTR, KIND_REP,   KIND_ROL,  KIND_ROR, 
                      KIND_SEXT, KIND_ZEXT, KIND_BVNEG, KIND_BVNOT):
            for c in children:
                if not c.sort.is_bv_sort:
                    raise DDSMTParseCheckException (
                        "'{!s}' expects BV sort as argument(s)".format(fun))
        # args equal sort check
        elif kind in (KIND_DIST, KIND_EQ):
            c0 = children[0]
            for c in children[1:]:
                if c.sort != c0.sort \
                   and c0.sort not in (sortint, sortreal) \
                   and c.sort not in (sortint, sortreal):
                    raise DDSMTParseCheckException (
                        "'{!s}' with mismatching sorts: '{!s}' '{!s}'" \
                        "".format(fun, c0.sort, c.sort)) 
        # args equal bw check
        elif kind in (KIND_BVADD,  KIND_BVAND,  KIND_BVASHR, KIND_BVCOMP, 
                      KIND_BVLSHR, KIND_BVMUL,  KIND_BVNAND, KIND_BVNOR,
                      KIND_BVOR,   KIND_BVSDIV, KIND_BVSGE,  KIND_BVSGT,  
                      KIND_BVSHL,  KIND_BVSLE,  KIND_BVSLT,  KIND_BVSMOD, 
                      KIND_BVSREM, KIND_BVSUB,  KIND_BVUGE,  KIND_BVUGT,  
                      KIND_BVUDIV, KIND_BVULE,  KIND_BVULT,  KIND_BVUREM, 
                      KIND_BVXNOR, KIND_BVXOR):
            c0 = children[0]
            if not c0.sort.is_bv_sort:
                raise DDSMTParseCheckException (
                    "'{!s}' expects BV sort as argument(s)".format(fun))
            for c in children[1:]:
                if c.sort != c0.sort:
                    raise DDSMTParseCheckException (
                        "'{!s}' with mismatching sorts: '{!s}' '{!s}'" \
                        "".format(fun, c0.sort, c.sort)) 
        # first arg Array check
        elif kind in (KIND_SELECT, KIND_STORE):
            if not children[0].sort.is_arr_sort:
                raise DDSMTParseCheckException (
                    "'{!s}' expects Array sort as first argument".format(fun))
        # ITE arg check
        elif kind == KIND_ITE:
            if not children[0].sort == sortbool:
                raise DDSMTParseCheckException (
                    "'{!s}' expects sort 'Bool' as first argument".format(fun))
            if children[1].sort != children[2].sort            \
               and children[1].sort not in (sortreal, sortint) \
               and children[2].sort not in (sortreal, sortint):
                    raise DDSMTParseCheckException (
                        "'ite' with mismatching sorts: '{!s}' '{!s}'"\
                        "".format(children[1].sort, children[2].sort)) 
        # not predefined
        else:
            declfun = self.find_fun(fun.name, fun.indices)
            assert (declfun)
            if declfun.sort == None:  # not declared yet
                raise DDSMTParseCheckException (
                        "function '{!s}' undeclared".format(fun))
            else:
                if len(children) != len(declfun.sorts):
                    raise DDSMTParseCheckException (
                            "'{!s}' expects {} argument(s), {} given".format(
                                declfun, len(declfun.sorts), len(children)))
                for i in range(len(children)):
                    if children[i].sort != declfun.sorts[i] \
                       and (declfun.sorts[i] != sortreal \
                            or children[i].sort != sortint):
                        raise DDSMTParseCheckException (
                            "'{!s}' with incompatible sort " \
                            "(expects '{!s}'): '{!s}'".format(
                                declfun, declfun.sorts[i], children[i].sort))

    def funApp2sort (self, fun, kind, children):
        self.check_funApp(fun, kind, children)
        # sort Bool
        if kind in (KIND_AND,   KIND_IMPL,  KIND_NOT,   KIND_OR,    KIND_XOR, 
                    KIND_EQ,    KIND_DIST,  KIND_LE,    KIND_LT,    KIND_GE,
                    KIND_GT,    KIND_ISI,   KIND_BVSGE, KIND_BVSGT, KIND_BVSLE,
                    KIND_BVSLT, KIND_BVUGE, KIND_BVUGT, KIND_BVULE, KIND_BVULT):
            return self.sortNode("Bool")
        # sort Int
        elif kind in (KIND_ABS, KIND_DIV, KIND_MOD):
            return self.sortNode("Int")
        # sort Real
        elif kind in (KIND_RDIV, KIND_TOI, KIND_TOR):
            return self.sortNode("Real")
        # sort BV sort != children sort
        elif kind == KIND_CONC:
            return self.bvSortNode(
                       children[0].sort.bw + children[1].sort.bw)
        elif kind == KIND_EXTR:
            return self.bvSortNode(fun.indices[0] - fun.indices[1] + 1)
        elif kind == KIND_REP:
            return self.bvSortNode(fun.indices[0] * children[0].sort.bw)
        elif kind in (KIND_SEXT, KIND_ZEXT):
            return self.bvSortNode(fun.indices[0] + children[0].sort.bw)
        elif kind == KIND_BVCOMP:
            return self.bvSortNode(1)
        # sort defined by children
        elif kind in (KIND_ADD, KIND_MUL, KIND_NEG, KIND_SUB):
            if True in [c.sort == self.sortNode("Real") for c in children]:
                return self.sortNode("Real")
            return children[0].sort
            
        elif kind in (KIND_NEG,    KIND_ROL,    KIND_ROR,    KIND_BVADD,
                      KIND_BVAND,  KIND_BVASHR, KIND_BVLSHR, KIND_BVMUL,
                      KIND_BVNAND, KIND_BVNEG,  KIND_BVNOR,  KIND_BVNOT,
                      KIND_BVOR,   KIND_BVSDIV, KIND_BVSHL,  KIND_BVSMOD,
                      KIND_BVSREM, KIND_BVSUB,  KIND_BVUDIV, KIND_BVUREM, 
                      KIND_BVXNOR, KIND_BVXOR):
            return children[0].sort
        # special cases
        elif kind == KIND_ITE: 
            if True in [c.sort == self.sortNode("Real") for c in children[1:]]:
                return self.sortNode("Real")
            return children[1].sort
        elif kind == KIND_SELECT:
            return children[0].sort.elem_sort
        elif kind == KIND_STORE:
            return children[0].sort
        return fun.sort

    def funAppNode (self, fun, children):
        global g_fun_kinds
        kind = fun.kind
        if fun.name in g_fun_kinds:
            if fun.name == '-' and len(children) == 1:
                kind = KIND_NEG
            else:
                kind = fun.name
        sort = self.funApp2sort(fun, kind, children)
        return SMTFunAppNode (fun, kind, sort, children)

    def letFeNode (self, kind, children, svars = None):
        assert (kind in (KIND_LET, KIND_FORALL, KIND_EXISTS))
        assert (kind != KIND_LET or svars == None)
        assert ((kind == KIND_LET and len(children) == 2) or
                (kind in (KIND_FORALL, KIND_EXISTS) and len(children) == 1))
        if kind == KIND_LET:
            assert (self.__assert_varb)
            # flatten children
            ch = []
            ch.extend(children[0])
            ch.append(children[1])
        else:
            assert (self.__assert_svar)
            assert (self.cur_scope.kind == KIND_FESCOPE)
            ch = children
        self.close_scope()
        return SMTLetNode (ch) if kind == KIND_LET \
                               else SMTForallExistsNode (svars, kind, ch)
    
    def annNode (self, attributes, sort, children):
        for attrib in attributes:
            attrib = attrib.split()
            if attrib[0] == ":named":
                if len(attrib) != 2:
                    raise DDSMTParseCheckException (
                            "missing attribute value for ':named'")
                name = attrib[1]
                fun = self.find_fun (name, [], self.cur_scope, True)
                if fun:
                    raise DDSMTParseCheckException (
                            "previous declaration of function {} was here" \
                            "".format(name))
                self.cur_scope.funs[name] = SMTAnnNode (
                        attributes, sort, children, name)
                if name in self.funs_cache:
                    self.funs_cache[name].append(self.cur_scope)
                else:
                    self.funs_cache[name] = [self.cur_scope]
                self.anns_cache.append(self.cur_scope.funs[name])
                return self.cur_scope.funs[name]
        return SMTAnnNode (attributes, sort, children)


    def cmdNode (self, kind, children = []):
        assert (self.cur_scope != None)
        cmd = None
        if kind == KIND_PUSH:
            assert (len(children) == 1)
            assert (isinstance (children[0], SMTConstNode))
            cmd = SMTPushCmdNode (children[0].value)
            self.cur_scope.cmds.append(cmd)
            cmd.scope = self.open_scope(cmd.nscopes)
        elif kind == KIND_POP:
            assert (len(children) == 1)
            assert (isinstance (children[0], SMTConstNode))
            cmd = SMTPopCmdNode (children[0].value)
            self.cur_scope.cmds.append(cmd)
            self.close_scope (cmd.nscopes)
        else:
            cmd = SMTCmdNode (kind, children)
            self.cur_scope.cmds.append(cmd)
        return cmd

    def add_fresh_declfunCmdNode (self, sort):
        name = "_substvar_{}_".format(len(self.scopes.declfun_cmds))
        fun = self.add_fun (name, sort, [], [])
        self.scopes.declfun_cmds[name] = SMTCmdNode (KIND_DECLFUN, [fun])
        return fun

    def __assert_varb (self, var_bindings):
        for varb in var_bindings:
            assert (varb.scope.kind == KIND_VSCOPE)
            assert (varb.scope == self.cur_scope)
            assert (self.find_fun(
                varb.var.name, varb.var.indices, self.cur_scope))
        return True     

    def __assert_svar (self, sorted_vars):
        for svar in sorted_vars:
            assert (svar.scope == KIND_SCOPE)
            assert (svar.scope == self.cur_scope)
            assert (self.find_fun(
                svar.var.name, svar.var.indices, self.cur_scope))
        return True



class DDSMTParser (SMTParser):
    
    def __init__ (self):
        super().__init__()
        self.smtformula = SMTFormula()
        self.__set_parse_actions()

    def parse (self, infile):
        try:
            super().parse(infile)
        except SMTParseException as e:
            raise DDSMTParseException (e.msg, e.parser)
        SMTNode.g_smtformula = self.smtformula
        SMTCmdNode.g_smtformula = self.smtformula
        SMTScopeNode.g_smtformula = self.smtformula
        return self.smtformula

    def __set_parse_actions (self):
        sf = self.smtformula
        try:
            self.numeral.set_parse_action (lambda t:
                    sf.constNode (
                        KIND_CONSTN, sf.sortNode ("Int"), int(t[0])))

            self.decimal.set_parse_action (lambda t:
                    sf.constNode (
                        KIND_CONSTD, sf.sortNode ("Real"), float(t[0])))

            self.hexadecimal.set_parse_action (lambda t:
                    sf.bvConstNode (
                        KIND_CONSTH, 
                        len(t[0][2:]) * 4,   # bw
                        int(t[0][2:], 16)))  # value

            self.binary.set_parse_action (lambda t:
                    sf.bvConstNode (
                        KIND_CONSTB,
                        len(t[0][2:]),       # bw
                        int(t[0][2:], 2)))   # value

            self.string.set_parse_action (lambda t:
                    sf.constNode (KIND_CONSTS, sf.sortNode ("String"), t[0]))

            self.b_value.set_parse_action (lambda t: sf.boolConstNode (t[0]))

            self.symbol.set_parse_action (lambda t: str(t))
            self.keyword.set_parse_action (lambda t: str(t))
            
            self.spec_constant.set_parse_action (lambda t: t[0])

            self.s_expr.set_parse_action (lambda t:
                    "({})".format(" ".join([str(to) for to in t[1]])) \
                            if t[0] == SMTParser.LPAR else t[0])

            self.sort.set_parse_action (self.__sort2SMTNode)
            self.sort_expr.set_parse_action (self.__sortExpr2SMTNode)
            
            self.attr_value.set_parse_action (lambda t:
                    "({})".format(" ".join([str(to) for to in t[1]])) \
                            if t[0] == SMTParser.LPAR else t[0])

            self.attribute.set_parse_action (lambda t: 
                    " ".join([str(to) for to in t]))

            self.qual_ident.set_parse_action (self.__qualIdent2SMTNode)
            
            self.var_binding.set_parse_action(self.__varBinding2SMTNode)

            self.sorted_var.set_parse_action (lambda t:
                    sf.funNode (str(t[0]), t[1], [], [], sf.cur_scope, False))

            self.sorted_qvar.set_parse_action(self.__sortedQVar2SMTNode)

            self.var_bindings.set_parse_action (self.__varBindings)
            self.sorted_qvars.set_parse_action (self.__sortedQVars)

            self.term.set_parse_action (self.__term2SMTNode)

            self.option.set_parse_action (lambda t: 
                    " ".join([str(to) for to in t]))

            self.command.set_parse_action (self.__cmd2SMTCmdNode)

        except DDSMTParseCheckException as e:
            raise DDSMTParseException (e.msg, e.parser)

    def __sort2SMTNode (self, t):
        sf = self.smtformula
        try:
            if len(t) == 1:
                t_ident = t[0]
                if t_ident[0] == SMTParser.IDXED:
                    assert (len(t_ident) == 3)
                    assert (len(t_ident[2]) == 1)
                    assert (isinstance(t_ident[2][0], SMTConstNode))
                    return sf.bvSortNode (t_ident[2][0].value)
                else:
                    assert (len(t_ident) == 1)
                    assert (type(t_ident[0]) == str)
                    return sf.sortNode (t_ident[0])
            else:
                assert (t[0] == SMTParser.LPAR)
                assert (len(t[1]) == 1)  # none but bv sorts are indexed
                t_ident = t[1]
                t_sorts = t[2]
                if str(t_ident) == "Array":
                    assert (len(t_sorts) == 2)
                    assert (isinstance(t_sorts[0], SMTSortNode))
                    assert (isinstance(t_sorts[1], SMTSortNode))
                    return sf.arrSortNode (t_sorts[0], t_sorts[1])
                return sf.sortNode (
                        "({} {})".format(
                            str(t_ident), " ".join([str(s) for s in t_sorts])),
                        len(t_sorts))
        except DDSMTParseCheckException as e:
            raise DDSMTParseException (e.msg, self)


    def __sortExpr2SMTNode (self, t):
        sf = self.smtformula
        try:
            if t[0] != SMTParser.LPAR:
                assert (len(t) == 1)
                t_ident = t[0]
                if t_ident[0] == SMTParser.IDXED:
                    assert (len(t_ident) == 3)
                    assert (len(t_ident[2]) == 1)
                    assert (isinstance(t_ident[2][0], SMTConstNode))
                    return SMTSortExprNode (sf.bvSortNode (t_ident[2][0].value))
                else:
                    assert (len(t_ident) == 1)
                    assert (type(t_ident[0]) == str)
                    return SMTSortExprNode (sf.sortNode (str(t_ident)))
            else:
                assert (len(t[1]) == 1)  # none but bv sorts are indexed
                t_ident = t[1]
                t_sorts = t[2]
                if str(t_ident) == "Array":
                    assert (len(t_sorts) == 2)
                    assert (isinstance(t_sorts[0], SMTSortNode))
                    assert (isinstance(t_sorts[1], SMTSortNode))
                    return SMTSortExprNode (
                            sf.arrSortNode (), 
                            [str(t_sorts[0]), str(t_sorts[1])])
                sort = sf.sortNode (str(t_ident))
                if len(t_sorts) != sort.nparams:
                    raise DDSMTParseException (
                            "sort '{!s}' expects {} argument(s), {} given"\
                            "".format(sort, sort.nparams, len(t_sorts)),
                            self)
                return SMTSortExprNode (sort, t_sorts)
        except DDSMTParseCheckException as e:
            raise DDSMTParseException (e.msg, self)
    

    def __qualIdent2SMTNode (self, t):
        sf = self.smtformula
        try:
            if len(t) == 1:
                t_ident = t[0]
                if t_ident[0] == SMTParser.IDXED:
                    if str(t_ident[1]).find("bv") == 0 and sf.is_bv_logic():
                        assert (len(t_ident) == 3)
                        assert (len(t_ident[2]) == 1)
                        assert (isinstance(t_ident[2][0], SMTConstNode))
                        return sf.bvConstNode (
                                KIND_CONSTN, t_ident[2][0].value, 
                                int(t_ident[1][2:]))
                    else:
                        assert (len(t_ident) > 1)
                        return sf.funNode (
                                str(t_ident[1]), None, [], t_ident[2],
                                sf.cur_scope)
                else:
                    return sf.funNode (str(t_ident), None, scope = sf.cur_scope)
            else:
                assert (t[0] == SMTParser.AS)
                t_ident = t[1]
                t_sort = t[2]
                if t_ident[0] == SMTParser.IDXED:
                    return sf.anFunNode (
                            str(t_ident[1]), t_sort, t_ident[2])
                else:
                    assert (len(t_ident) == 1)
                    return sf.anFunNode (str(t_ident), t_sort, [])
        except DDSMTParseCheckException as e:
            raise DDSMTParseException (e.msg, self)
    
    def __varBinding2SMTNode (self, t, cnt = 1):
        sf = self.smtformula
        if cnt == 1:  # open scope at first var binding
            sf.open_scope(kind = KIND_LSCOPE)
        varb = SMTVarBindNode (
                sf.funNode (str(t[0]), t[1].sort, [], [], sf.cur_scope, False), 
                [t[1]])
        return varb

    def __sortedQVar2SMTNode (self, t, cnt = 1):
        sf = self.smtformula
        if cnt == 1:  # open scope at first sorted var
            sf.open_scope(kind = KIND_FESCOPE)
        svar = SMTSortedQVarNode (
                sf.funNode (str(t[0]), t[1], [], [], sf.cur_scope, False))
        return svar

    def __varBindings (self, t):
        assert (len(t) == 1)
        assert (isinstance(t[0], list))
        assert (isinstance(t[0][0], SMTVarBindNode))
        return t[0]

    def __sortedQVars (self, t):
        assert (len(t) == 1)
        assert (isinstance(t[0], list))
        assert (isinstance(t[0][0], SMTSortedQVarNode))
        return t[0]

    def __term2SMTNode (self, t):
        sf = self.smtformula
        try:
            if len(t) == 1:
                return t[0]
            if t[0] == SMTParser.LET:
                assert (len(t) == 3)
                return sf.letFeNode (KIND_LET, [t[1], t[2]])
            elif t[0] in (SMTParser.FORALL, SMTParser.EXISTS):
                assert (len(t) == 3)
                return sf.letFeNode (t[0], [t[2]], t[1])
            elif t[0] == SMTParser.EXCL:
                assert (len(t) == 3)
                return sf.annNode (t[2], t[1].sort, [t[1]])
            else:
                assert (isinstance(t[0], SMTFunNode))
                return sf.funAppNode (t[0], t[1])
        except DDSMTParseCheckException as e:
            raise DDSMTParseException (e.msg, self)

    def __cmd2SMTCmdNode (self, t):
        sf = self.smtformula
        kind = t[0]
        if kind == KIND_SETLOGIC:
            assert (len(t) == 2)
            sf.logic = t[1]
        if kind == KIND_DECLSORT:
            assert (len(t) == 3)
            sort = sf.find_sort (t[1])
            if sort and sort.params != t[2].value:
               (line, col) = self.get_pos()
               raise DDSMTParseException (
                        "previous declaration of sort '{}' with '{}' "\
                        "was here".format(t[1], t[2].value),
                        self)
            if not sort:
                sort = sf.sortNode (t[1], t[2].value, sf.cur_scope, True)
            return sf.cmdNode (KIND_DECLSORT, [sort])
        elif kind == KIND_DEFSORT:
            assert (len(t) == 4)
            assert (isinstance (t[3], SMTSortExprNode))
            sort = sf.sortNode (t[1], t[3].sort.nparams, sf.cur_scope, True)
            return sf.cmdNode (
                    KIND_DEFSORT, [sort, [str(to) for to in t[2]], t[3]])
        elif kind == KIND_DECLFUN:
            assert (len(t) == 4)
            # fun has been added to scope level 0 when recursively stepping
            # through declare-fun -> move to cur_scope
            fun = sf.find_fun(t[1], t[3])
            if fun:
                (line, col) = self.get_pos()
                raise DDSMTParseException (
                         "previous declaration of function '{!s}'"\
                         "was here".format(fun),
                         self)
            fun = sf.funNode (t[1], t[3], t[2][0:], [], sf.cur_scope)
            return sf.cmdNode (KIND_DECLFUN, [fun])
        elif kind == KIND_DEFFUN:
            assert (len(t) == 5)
            sorts = [to.sort for to in t[2]]
            return sf.cmdNode (
                    KIND_DEFFUN,
                    [sf.funNode (t[1], t[3], sorts, [], sf.cur_scope), 
                     t[2], t[4]])
        elif kind == KIND_GETVALUE:
            assert (len(t) == 2)
            return sf.cmdNode (KIND_GETVALUE, [t[1]])
        else:
            return sf.cmdNode (kind, children = t[1:])
