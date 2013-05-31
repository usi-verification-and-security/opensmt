#! /usr/bin/env python3
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

import os
import sys
import shutil
import time
import random

from argparse import ArgumentParser, REMAINDER
from subprocess import Popen, PIPE
from parser.ddsmtparser import DDSMTParser, DDSMTParseException


__version__ = "0.92-beta"
__author__  = "Aina Niemetz <aina.niemetz@gmail.com>"


g_golden = 0
g_ntests = 0

g_args = None
g_smtformula = None
g_tmpfile = "/tmp/tmp-" + str(os.getpid()) + ".smt2"



class DDSMTException (Exception):

    def __init__ (self, msg):
        self.msg = msg
    
    def __str__ (self):
        return "[ddsmt] Error: {0:s}".format(self.msg)



def _cleanup():
    if os.path.exists(g_tmpfile):
        os.remove(g_tmpfile)


def _log(verbosity, msg = "", update = False):
    global g_args
    if g_args.verbosity >= verbosity:
        sys.stdout.write(" " * 80 + "\r")
        if update:
            sys.stdout.write("[ddsmt] {0:s}\r".format(msg))
            sys.stdout.flush()
        else:
            sys.stdout.write("[ddsmt] {0:s}\n".format(msg))


def _dump (filename = None, root = None):
    global g_smtformula
    assert (g_smtformula)
    try:
        g_smtformula.dump(filename, root)
    except IOError as e:
        raise DDSMTException (str(e))


def _run ():
    global g_args
    try:
        start = time.time()
        sproc = Popen(g_args.cmd, stdout=PIPE, stderr=PIPE)

        # TODO this works from 3.3 upwards
        # (out, err) = sproc.communicate(g_opts.timeout)  # TODO use out, err
        
        # TODO disable this from 3.3. upwards
        if g_args.timeout:
            while (sproc.poll() == None):
                if time.time() - start > g_args.timeout:
                    sproc.kill()
                time.sleep(1)

        (out, err) = sproc.communicate()
        _log (3)
        _log (3, "solver output: " + out.decode())
        return sproc.returncode

    # TODO this works from 3.3 upwards
    #except TimeoutExpired as e:
    #    sproc.kill()
    #    (out, err) = proc.communicate()
    except OSError as e:
        raise DDSMTException ("{0:s}: {1:s}".format(str(e), g_cmd[0]))


def _test ():
    global g_args, g_ntests
    # TODO compare output if option enabled?
    g_ntests += 1
    return _run() == g_golden


def _filter_scopes (filter_fun = None, root = None):
    global g_smtformula
    assert (g_smtformula)
    scopes = []
    to_visit = [root if root != None else g_smtformula.scopes]
    
    while to_visit:
        cur = to_visit.pop()
        if cur.is_subst():
            continue
        if filter_fun == None or filter_fun(cur):
            scopes.append(cur)
        to_visit.extend(cur.scopes) 
    return scopes


def _filter_cmds (filter_fun = None, root = None):
    cmds = []
    scopes = _filter_scopes (lambda x: x.is_regular())
    to_visit = [c for cmd_list in [s.cmds for s in scopes] for c in cmd_list]
    to_visit.extend(g_smtformula.scopes.declfun_cmds.values())
    while to_visit:
        cur = to_visit.pop()
        if cur.is_subst():
            continue
        if filter_fun == None or filter_fun(cur):
            cmds.append(cur)
    return cmds


def _filter_terms (filter_fun = None, root = None):
    nodes = []
    to_visit = [root]
    if not root:
        asserts = _filter_cmds (lambda x: x.is_assert())
        to_visit = [c.children[0] for c in asserts \
                if not c.children[0].get_subst().is_const()]
    while to_visit:
        cur = to_visit.pop().get_subst()
        if filter_fun == None or filter_fun(cur):
            nodes.append(cur)
        if cur.children:
            to_visit.extend(cur.children)
    
    nodes.sort(key = lambda x: x.id)
    return nodes


def _substitute (subst_fun, substlist, superset, with_vars = False):
    global g_smtformula
    assert (g_smtformula)
    assert (substlist in (g_smtformula.subst_scopes, g_smtformula.subst_cmds, 
                          g_smtformula.subst_nodes))
    nsubst_total = 0
    gran = len(superset)

    while gran > 0:
        subsets = [superset[s:s+gran] for s in range (0, len(superset), gran)]
        cpy_subsets = subsets[0:]

        for subset in subsets:
            nsubst = 0
            cpy_substs = substlist.substs.copy()
            cpy_declfun_cmds = g_smtformula.scopes.declfun_cmds.copy()
            for item in subset:
                if not item.is_subst():
                    item.subst (subst_fun(item))
                    nsubst += 1
            if nsubst == 0:
                continue
            
            _dump (g_tmpfile)
           
            if _test():
                _dump (g_args.outfile)
                nsubst_total += nsubst
                _log (2, "  granularity: {}, subsets: {}, substituted: {}" \
                         "".format(gran, len(subsets), nsubst), True)
                del (cpy_subsets[cpy_subsets.index(subset)])
            else:
                _log (2, "  granularity: {}, subsets: {}, substituted: 0" \
                         "".format(gran, len(subsets)), True)
                substlist.substs = cpy_substs
                if with_vars:
                    for name in g_smtformula.scopes.declfun_cmds:
                        assert (g_smtformula.find_fun(name))
                        if name not in cpy_declfun_cmds:
                            g_smtformula.delete_fun(name)
                g_smtformula.scopes.declfun_cmds = cpy_declfun_cmds
        superset = [s for subset in cpy_subsets for s in subset]
        gran = gran // 2
    return nsubst_total


def _substitute_scopes ():
    global g_smtformula
    assert (g_smtformula)

    _log (2)
    _log (2, "substitute SCOPES:")

    nsubst_total = 0
    level = 1
    while True:
        scopes = _filter_scopes (lambda x: x.level == level and x.is_regular())
        if not scopes:
            break

        nsubst_total += _substitute (
                lambda x: None, g_smtformula.subst_scopes, scopes)
        level += 1
        
    _log (2, "  >> {0:d} scope(s) substituted in total".format(nsubst_total))
    return nsubst_total

        
def _substitute_cmds (filter_fun = None):
    global g_smtformula
    assert (g_smtformula)

    _log (2)
    _log (2, "substitute COMMANDS:")

    filter_fun = filter_fun if filter_fun else \
            lambda x: not x.is_setlogic() and not x.is_exit()

    nsubst_total = _substitute (lambda x: None, g_smtformula.subst_cmds,
            _filter_cmds(filter_fun))

    _log (2, "  >> {0:d} command(s) substituted in total".format(nsubst_total))
    return nsubst_total


def _substitute_terms (subst_fun, filter_fun, cmds = None, msg = None, 
                       with_vars = False):
    _log (2)
    _log (2, msg if msg else "substitute TERMS:")

    nsubst_total = 0
    cmds = cmds if cmds else _filter_cmds (lambda x: x.is_assert())

    for cmd in cmds:
        assert (len(cmd.children) == 1)
        nsubst_total += _substitute (subst_fun, g_smtformula.subst_nodes,
            _filter_terms (filter_fun, cmd.children[0]), with_vars)

    _log (2, "  >> {0:d} term(s) substituted in total".format(nsubst_total))
    return nsubst_total


def ddsmt_main ():
    global g_tmpfile, g_args, g_smtformula

    nrounds = 0
    nsubst_total = 0
    nsubst_round = 1
    
    nscopes_subst = 0
    ncmds_subst = 0
    nterms_subst = 0

    succeeded = "none"
    
    while nsubst_round:
        nrounds += 1
        nsubst = 0
        nsubst_round = 0

        nsubst = _substitute_scopes ()
        if nsubst:
            succeeded = "scopes"
            nsubst_round += nsubst
            nscopes_subst += nsubst
        elif succeeded == "scopes":
            break
        
        # initially, eliminate asserts only
        # -> prevent lots of likely unsuccessful testing when eliminating
        #    e.g. declare-funs previous to term substitution
        if nrounds > 1:
           nsubst = _substitute_cmds ()
        else:
           nsubst = _substitute_cmds (lambda x: x.is_assert())
        if nsubst:
           succeeded = "cmds"
           nsubst_round += nsubst
           ncmds_subst += nsubst
        elif succeeded == "cmds": 
           break

        cmds = _filter_cmds (lambda x: x.is_assert())

        if g_smtformula.is_bv_logic():
            nsubst = _substitute_terms (
                    lambda x: g_smtformula.bvZeroConstNode(x.sort),
                    lambda x: 
                       x.sort and x.sort.is_bv_sort() and not x.is_const(),
                    cmds, "substitute BV TERMS with '0'")
            if nsubst:
                succeeded = "bv0"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "bv0":
                break
            nsubst = _substitute_terms (
                    lambda x: g_smtformula.add_fresh_declfunCmdNode (x.sort),
                    lambda x:
                        x.sort and x.sort.is_bv_sort() and not x.is_const() \
                        and (not x.is_fun() or not g_smtformula.is_substvar(x)),
                    cmds, "substitute BV TERMS with fresh variables", True)
            if nsubst:
                succeeded = "bvvar"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "bvvar": 
                break

        if g_smtformula.is_int_logic() or g_smtformula.is_real_logic():
            nsubst = _substitute_terms (
                    lambda x: g_smtformula.zeroConstNNode(),
                    lambda x: x.sort == g_smtformula.sortNode("Int") \
                              and not x.is_const(),
                    cmds, "substitute Int Terms with '0'")
            if nsubst:
                succeeded = "int0"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "int0":
                break
            nsubst = _substitute_terms (
                    lambda x: g_smtformula.add_fresh_declfunCmdNode (x.sort),
                    lambda x: x.sort == g_smtformula.sortNode("Int") \
                              and not x.is_const(),
                    cmds, "substitute Int TERMS with fresh variables", True)
            if nsubst:
                succeeded = "intvar"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "intvar": 
                break

        if g_smtformula.is_real_logic():
            nsubst = _substitute_terms (
                    lambda x: g_smtformula.zeroConstDNode(),
                    lambda x: x.sort == g_smtformula.sortNode("Real") \
                              and not x.is_const(),
                    cmds, "substitute Real Terms with '0'")
            if nsubst:
                succeeded = "real0"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "real0":
                break
            nsubst = _substitute_terms (
                    lambda x: g_smtformula.add_fresh_declfunCmdNode (x.sort),
                    lambda x: x.sort == g_smtformula.sortNode("Real") \
                              and not x.is_const(),
                    cmds, "substitute Real TERMS with fresh variables", True)
            if nsubst:
                succeeded = "realvar"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "realvar":
                break

        nsubst = _substitute_terms (
                lambda x: x.children[-1],
                lambda x: x.is_let(),
                cmds, "substitute LETs with child term")
        if nsubst:
            succeeded = "let"
            nsubst_round += nsubst
            nterms_subst += nsubst
        elif succeeded == "let":
            break

        nsubst = _substitute_terms (
                lambda x: g_smtformula.boolConstNode("false"), 
                lambda x: x.sort == g_smtformula.sortNode("Bool") \
                          and not x.is_const(), 
                cmds, "substitute Boolean TERMS with 'false'")
        if nsubst:
            succeeded = "false"
            nsubst_round += nsubst
            nterms_subst += nsubst
        elif succeeded == "false":
            break

        nsubst = _substitute_terms (
                lambda x: g_smtformula.boolConstNode("true"), 
                lambda x: x.sort == g_smtformula.sortNode("Bool") \
                          and not x.is_const(), 
                cmds, "substitute Boolean TERMS with 'true'")
        if nsubst:
            succeeded = "true"
            nsubst_round += nsubst
            nterms_subst += nsubst
        elif succeeded == "true":
            break

        if g_smtformula.is_arr_logic():
            nsubst = _substitute_terms (
                    lambda x: x.children[0],  # array
                    lambda x: x.is_write(),
                    cmds, "substitute STOREs with array child")
            if nsubst:
                succeeded = "store"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "store":
                break
            nsubst = _substitute_terms (
                    lambda x: x.children[1],  # array
                    lambda x: x.is_read(),
                    cmds, "substitute SELECTs with index child")
            if nsubst:
                succeeded = "select"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "select":
                break
            nsubst = _substitute_terms (
                    lambda x: x.children[1],  # left child
                    lambda x: x.is_ite(),
                    cmds, "substitute ITE with left child")
            if nsubst:
                succeeded = "iteleft"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "iteleft":
                break
            nsubst = _substitute_terms (
                    lambda x: x.children[2],  # right child
                    lambda x: x.is_ite(),
                    cmds, "substitute ITE with right child")
            if nsubst:
                succeeded = "iteright"
                nsubst_round += nsubst
                nterms_subst += nsubst
            elif succeeded == "iteright":
                break

        nsubst_total += nsubst_round

    _log (1)
    _log (1, "rounds total: {}".format(nrounds))
    _log (1, "tests  total: {}".format(g_ntests))
    _log (1, "substs total: {}".format(nsubst_total))
    _log (1)
    _log (1, "scopes substituted: {}".format(nscopes_subst))
    _log (1, "cmds   substituted: {}".format(ncmds_subst))
    _log (1, "terms  substituted: {}".format(nterms_subst))

    if nsubst_total == 0:
        sys.exit ("[ddsmt] unable to reduce input file")


if __name__ == "__main__":
    try:
        usage="ddsmt.py [<options>] <infile> <outfile> <cmd> [<cmd options>]"
        aparser = ArgumentParser (usage=usage)
        aparser.add_argument ("infile", 
                              help="the input file (in SMT-LIB v2 format)")
        aparser.add_argument ("outfile",
                              help="the output file")
        aparser.add_argument ("cmd", nargs=REMAINDER, 
                              help="the command (with optional arguments)")

        aparser.add_argument ("-t", dest="timeout", metavar="val",
                              default=None, type=int, 
                              help="timeout for test runs in seconds "\
                                   "(default: none)")
        aparser.add_argument ("-v", action="count", default=0, 
                              dest="verbosity", help="increase verbosity")
        aparser.add_argument ("-o", action="store_true", dest="optimize",
                              default=False, 
                              help="remove assertions and debug code")
        aparser.add_argument ("--version", action="version", 
                              version=__version__)
        g_args = aparser.parse_args()

        if not g_args.cmd:  # special handling (nargs=REMAINDER)
            raise DDSMTException ("too few arguments")
        
        if g_args.optimize:
            sys.argv.remove("-o")
            os.execl(sys.executable, sys.executable, '-O', *sys.argv)
        else:
            if not os.path.exists(g_args.infile):
                raise DDSMTException ("given input file does not exist")
            if os.path.isdir(g_args.infile):
                raise DDSMTException ("given input file is a directory")
            if os.path.exists(g_args.outfile):
                raise DDSMTException ("given output file does already exist")

            _log (1, "input  file: '{}'".format(g_args.infile))
            _log (1, "output file: '{}'".format(g_args.outfile))
            _log (1, "command:     '{}'".format(
                " ".join([str(c) for c in g_args.cmd])))

            ifilesize = os.path.getsize(g_args.infile)

            parser = DDSMTParser()
            g_smtformula = parser.parse(g_args.infile)

            _log (2, "parser done")

            shutil.copyfile(g_args.infile, g_tmpfile)
            g_args.cmd.append(g_tmpfile)
            g_golden = _run()
            
            _log (1)
            _log (1, "golden exit: {0:d}".format(g_golden))

            ddsmt_main ()
            
            ofilesize = os.path.getsize(g_args.outfile)

            _log (1)
            _log (1, "input file size:  {} B (100%)".format(ifilesize))
            _log (1, "output file size: {} B ({:3.2f}%)".format(
                ofilesize, ofilesize / ifilesize * 100))
            _cleanup()
            sys.exit(0)
    except (DDSMTParseException, DDSMTException) as e:
        _cleanup()
        sys.exit(str(e))
    except MemoryError as e:
        _cleanup()
        sys.exit("[ddsmt] memory exhausted")
    except KeyboardInterrupt as e:
        _cleanup()
        sys.exit("[ddsmt] interrupted")
