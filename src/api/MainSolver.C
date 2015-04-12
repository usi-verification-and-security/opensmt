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


#include "MainSolver.h"
#include "TreeOps.h"
#include "DimacsParser.h"
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#ifdef USE_GZ
#include <zlib.h>
#include <stdio.h>
#endif

#ifdef USE_GZ
#if defined(MSDOS) || defined(OS2) || defined(WIN32) || defined(__CYGWIN__)
#include <fcntl.h>
#include <io.h>
#define SET_BINARY_MODE(file) setmode(fileno(fil), O_BINARY)
#else
#define SET_BINARY_MODE(file)
#endif
#define CHUNK_SZ 1048576
#endif

#ifdef USE_GZ
int MainSolver::compress_buf(const int* buf_in, int*& buf_out, int sz, int& sz_out) const
{
    unsigned char* in = (unsigned char*) buf_in;
    unsigned char* out = (unsigned char*) buf_out;

    z_stream strm;
    int ret, flush;
    unsigned have;

    int out_buf_sz = CHUNK_SZ;
    out = (unsigned char*)malloc(out_buf_sz);

    int in_buf_p  = 0;
    int out_buf_p = 0;

    strm.zalloc  = Z_NULL;
    strm.zfree   = Z_NULL;
    strm.opaque  = Z_NULL;
    ret = deflateInit(&strm, Z_DEFAULT_COMPRESSION);
    if (ret != Z_OK)
        return ret;

    // Compress buf_in until sz chars have been processed
    int bytes_left = sz;

    do {
        int in_buf_sz = bytes_left < sz ? bytes_left : sz;
        flush = bytes_left <= sz ? Z_FINISH : Z_NO_FLUSH;

        strm.next_in = in + in_buf_p;
        strm.avail_in = in_buf_sz;

        do {
            int avail_out = out_buf_sz - out_buf_p;
            if (avail_out == 0) {
                out_buf_sz += CHUNK_SZ;
                out = (unsigned char*)realloc(out, out_buf_sz);
                avail_out = out_buf_sz - out_buf_p;
            }
            strm.avail_out = avail_out;
            strm.next_out = out+out_buf_p;

            if ((ret = deflate(&strm, flush)) == Z_STREAM_ERROR)
                return Z_STREAM_ERROR;

            have = avail_out - strm.avail_out;
            out_buf_p += have;
        } while (strm.avail_out == 0);

        assert(strm.avail_in == 0);
    } while (flush != Z_FINISH);

    assert(ret == Z_STREAM_END);
    deflateEnd(&strm);

    out = (unsigned char*) realloc(out, out_buf_p);
    buf_out = (int*)out;
    sz_out = out_buf_p;
    return Z_OK;
}

int MainSolver::decompress_buf(int* buf_in, int*& buf_out, int sz, int& sz_out ) const
{
    int ret;
    unsigned have;
    z_stream strm;

    unsigned char* in = (unsigned char*) buf_in;
    unsigned char* out = (unsigned char*) buf_out;
    int out_p = 0;

    int out_sz = CHUNK_SZ;
    out = (unsigned char*) malloc(out_sz);


    strm.zalloc   = Z_NULL;
    strm.zfree    = Z_NULL;
    strm.opaque   = Z_NULL;
    strm.avail_in = 0;
    strm.next_in  = Z_NULL;

    ret = inflateInit(&strm);
    if (ret != Z_OK)
        return ret;

    do {
        strm.avail_in = sz;
        if (strm.avail_in == 0) break;
        strm.next_in = in;
        do {
            if (out_sz - out_p == 0) {
                out_sz += CHUNK_SZ;
                out = (unsigned char*) realloc(out, out_sz);
            }
            strm.avail_out = out_sz - out_p;
            strm.next_out = out + out_p;

            ret = inflate(&strm, Z_NO_FLUSH);
            assert(ret != Z_STREAM_ERROR);
            if (ret == Z_NEED_DICT) return Z_DATA_ERROR;
            if (ret == Z_DATA_ERROR) return ret;
            if (ret == Z_MEM_ERROR) return ret;

            have = (out_sz - out_p) - strm.avail_out;
            out_p += have;
        } while (strm.avail_out == 0);
    } while (ret != Z_STREAM_END);

    inflateEnd(&strm);
    sz_out = out_p;
    buf_out = (int*) out;

    return ret == Z_STREAM_END ? Z_OK : Z_DATA_ERROR;
}
#endif

sstat MainSolver::simplifyFormulas(char** err_msg) {
    status = s_Undef;
    PTRef  root;
    // Think of something here to enable incrementality...
    if (!ts.solverEmpty()) {
        asprintf(err_msg, "Solver already contains a simplified problem.  Cannot continue for now");
        return s_Error; }

    root = logic.mkAnd(formulas);
    PTRef trans = PTRef_Undef;
    trans = tlp.learnEqTransitivity(root);
    if (trans != PTRef_Undef) {
        vec<PTRef> enriched;
        enriched.push(trans);
        enriched.push(root);
        root = logic.mkAnd(enriched);
    }
    // Framework for handling different logic related simplifications.
    // For soundness it is important to run this until closure
    Map<PTRef,int,PTRefHash> subst_targets;
    while (true) {
        // For termination it is important to have this reinitialized
        // every time
        Map<PTRef,PTRef,PTRefHash> substs;
#ifdef SIMPLIFY_DEBUG
        cerr << "retrieving" << endl;
        vec<PTRef> subst_vars;
        tlp.retrieveSubstitutions(root, substs, subst_targets, subst_vars);
        cerr << "Identified substitutions: " << endl;
        for (int i = 0; i < subst_vars.size(); i++)
            cerr << "Substituting " << logic.printTerm(subst_vars[i]) << " with " << logic.printTerm(substs[subst_vars[i]]) << endl;
#else
        tlp.retrieveSubstitutions(root, substs, subst_targets);
#endif

//        if (!tlp.substitute(root)) break;
#ifdef SIMPLIFY_DEBUG
        cerr << "substituting" << endl;
#endif
#ifndef OLD_VARSUBSTITUTE
        PTRef new_root = PTRef_Undef;
        if (!tlp.varsubstitute(root, substs, subst_targets, new_root)) break;
        root = new_root;
#else
        if (!tlp.varsubstitute(root, substs)) break;
#endif
        lbool res = logic.simplifyTree(root);
        if (res == l_True) root = logic.getTerm_true(); // Trivial problem
        else if (res == l_False) root = logic.getTerm_false(); // Trivial problem
    }

    vec<PtAsgn> tlfacts;
#ifdef ENABLE_CONGRUENCESUBSTITUTION
#ifdef SIMPLIFY_DEBUG
    cerr << "Init congruence with " << logic.printTerm(root) << endl;
#endif
    tlp.initCongruence(root);

#ifdef SIMPLIFY_DEBUG
    cerr << "Compute congruence substitution" << endl;
#endif
    if (!tlp.computeCongruenceSubstitutions(root, tlfacts)) {
        root = logic.getTerm_false(); // trivial problem
    }
    PTRef new_root;
    tlp.substitute(root, new_root);
    root = new_root;
#endif
    {
        // Add the top level facts to the formula
        vec<PTRef> tmp;
        tmp.push(root);
        for (int i = 0; i < tlfacts.size(); i++)
            tmp.push(tlfacts[i].sgn == l_True ? tlfacts[i].tr : logic.mkNot(tlfacts[i].tr));
        root = logic.mkAnd(tmp);
        lbool res = logic.simplifyTree(root);
        if (res == l_True) root = logic.getTerm_true(); // Trivial problem
        else if (res == l_False) root = logic.getTerm_false(); // Trivial problem
        vec<PtChild> terms;
        FContainer fc(root);
        expandItes(fc, terms);
        fc.setRoot(terms[terms.size()-1].tr);

#ifdef OLD_SIMPLIFICATION
        // XXX There should be no reason to do this one by one, and in fact it
        // should be harmful since the shared structure will be invisible that
        // way.
        PTRef root = fc.getRoot();
        Pterm& r = logic.getPterm(root);
        vec<PTRef> tlfs;
        ts.retrieveTopLevelFormulae(root, tlfs);
        for (int i = 0; (i < tlfs.size()) && (status == s_Undef); i++) {
            if (ts.checkDeMorgan(tlfs[i]) || ts.checkCnf(tlfs[i]) || ts.checkClause(tlfs[i]))
                fc.setRoot(tlfs[i]);
            else {
                fc.setRoot(tlfs[i]);
                fc = propFlatten(fc);
            }
            terms.clear();
            getTermList(fc.getRoot(), terms, logic);
            fc = simplifyEqualities(terms);
            lbool res = logic.simplifyTree(fc.getRoot());
#ifdef SIMPLIFY_DEBUG
            cerr << "After simplification got " << endl;
            if (res == l_Undef)
                 cerr << logic.printTerm(fc.getRoot()) << endl;
            else if (res == l_False)
                cerr << logic.printTerm(logic.getTerm_false()) << endl;
            else if (res == l_True)
                cerr << logic.printTerm(logic.getTerm_true()) << endl;
            else
                assert(false);
#endif

            if (res == l_False) status = giveToSolver(logic.getTerm_false());
            else if (res == l_Undef)
                status = giveToSolver(fc.getRoot());
        }
#else
        fc = propFlatten(fc);
        terms.clear();
        getTermList(fc.getRoot(), terms, logic);
        fc = simplifyEqualities(terms);
        res = logic.simplifyTree(fc.getRoot());
        if (res == l_False) status = giveToSolver(logic.getTerm_false());
        else if (res == l_Undef)
            status = giveToSolver(fc.getRoot());
#endif

    }
    return status;
}

void MainSolver::expandItes(FContainer& fc, vec<PtChild>& terms) const
{
    // cnfization of the formula
    // Get the egraph data structure for instance from here
    // Terms need to be purified before cnfization?

    PTRef root = fc.getRoot();

    getTermList<PtChild>(root, terms, logic);

    if (terms.size() > 0) {
        root = ts.expandItes(terms);
        terms.clear();
        // This seems a bit subtle way of updating the terms vector
        getTermList<PtChild>(root, terms, logic);
    }
    fc.setRoot(root);
}


#ifdef ENABLE_SHARING_BUG
MainSolver::FContainer MainSolver::mergeEnodeArgs(PTRef fr, Map<PTRef, PTRef, PTRefHash>& cache, Map<PTRef, int, PTRefHash>& occs)
{
    assert(logic.isAnd(fr) || logic.isOr(fr));
    Pterm& f = logic.getPterm(fr);
    SymRef sr = f.symb();
    vec<PTRef> new_args;
#ifdef SIMPLIFY_DEBUG
    char* name = logic.printTerm(fr);
    cout << "; Merge: " << name << endl;
    ::free(name);
#endif
    for (int i = 0; i < f.size(); i++) {
        PTRef arg = f[i];
        PTRef sub_arg = cache[arg];
        SymRef sym = logic.getPterm(arg).symb();
        if (sym != sr) {
            new_args.push(sub_arg);
            continue;
        }
        assert(occs.contains(arg));
        assert(occs[arg] >= 1);

        if (occs[arg] > 1) {
            new_args.push(sub_arg);
#ifdef SIMPLIFY_DEBUG
            cout << " Using shared structure (" << occs[arg] << " * ";
            char* name = logic.printTerm(sub_arg);
            cout << name << endl;
            ::free(name);
#endif
            continue;
        }
        Pterm& sa = logic.getPterm(sub_arg);
        for (int j = 0; j < sa.size(); j++)
            new_args.push(sa[j]);
    }
    const char* msg;
    PTRef out = logic.mkFun(sr, new_args, &msg);
#ifdef SIMPLIFY_DEBUG
    cout << " =>    ";
    name = logic.printTerm(out);
    cout << name << endl;
    ::free(name);
#endif
    return out;
}

MainSolver::FContainer MainSolver::rewriteMaxArity(MainSolver::FContainer fc, Map<PTRef, int, PTRefHash>& occs)
{
    PTRef f = fc.getRoot();
    vec<PTRef> queue;
    queue.push(f);
    Map<PTRef,PTRef,PTRefHash> cache; // Cache for processed nodes

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        Pterm& t = logic.getPterm(tr);
        if (cache.contains(tr)) {
            queue.pop();
            continue;
        }

        bool unprocessed_children = false;
        for (int i = 0; i < t.size(); i++) {
            if (logic.isBooleanOperator(t[i]) && !cache.contains(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true;
            } else if (logic.isAtom(t[i]))
                cache.insert(t[i], t[i]);
        }
        if (unprocessed_children) continue;
        queue.pop();
        assert(logic.isBooleanOperator(tr) || logic.isTrue(tr) || logic.isFalse(tr));
        PTRef result;
        if (logic.isAnd(tr) || logic.isOr(tr))
            result = mergeEnodeArgs(tr, cache, occs).getRoot();
        else
            result = tr;

        assert(!cache.contains(tr));
        cache.insert(tr, result);
    }

    fc.setRoot(cache[f]);
    return fc;
}
#endif

//
// Replace subtrees consisting only of ands / ors with a single and / or term.
// Search a maximal section of the tree consisting solely of ands / ors.  The
// root of this subtree is called and / or root.  Collect the subtrees rooted at
// the leaves of this section, and create a new and / or term with the leaves as
// arguments and the parent of the and / or tree as the parent.
//
// However, we will do this in a clever way so that if a certain
// term appears as a child in more than one term, we will not flatten
// that structure.
//
MainSolver::FContainer MainSolver::propFlatten(MainSolver::FContainer fc)
{
#ifdef SIMPLIFY_DEBUG
    cerr << "; COMPUTE INCOMING EDGES" << endl;
#endif

    PTRef top = fc.getRoot();
    vec<pi> qu;
    qu.push(pi(top));
    Map<PTRef,int,PTRefHash> occs;
    vec<PTRef> terms;
#ifdef SIMPLIFY_DEBUG
    VecMap<PTRef,PTRef,PTRefHash > parents;
#endif

    while (qu.size() != 0) {
        int ci = qu.size() - 1;
#ifdef SIMPLIFY_DEBUG
        cerr << "Processing " << logic.printTerm(qu[ci].x) << " (" << qu[ci].x.x << ")" << endl;
#endif
//        assert(!occs.contains(qu[ci].x));
        if (occs.contains(qu[ci].x)) {
            // fires if a term has two occurrences of the same atom
#ifdef SIMPLIFY_DEBUG
            cerr << "Processed before: " << logic.printTerm(qu[ci].x);
#endif
            occs[qu[ci].x]++;
            qu.pop();
            continue;
        }
        bool unprocessed_children = false;
#ifdef ENABLE_SHARING_BUG
        if (logic.isBooleanOperator(qu[ci].x))
#else
        if (logic.isBooleanOperator(qu[ci].x) && qu[ci].done == false)
#endif
        {
            Pterm& t = logic.getPterm(qu[ci].x);
            for (int i = 0; i < t.size(); i++) {
                PTRef cr = t[i];
                if (!occs.contains(cr)) {
                    unprocessed_children = true;
                    qu.push(pi(cr));
                    vec<PTRef> tmp;
                    tmp.push(qu[ci].x);
#ifdef SIMPLIFY_DEBUG
                    parents.insert(cr,tmp);
#endif
                }
                else {
#ifdef SIMPLIFY_DEBUG
                    Pterm& c = logic.getPterm(cr);
                    cerr << "Node id " << c.getId() << " Processed before 2: " << logic.printTerm(cr) << endl;
                    cerr << "Current parent is " << logic.printTerm(qu[ci].x) << endl;
#endif
                    occs[cr]++;
#ifdef SIMPLIFY_DEBUG
                    parents[cr].push(qu[ci].x);
                    cerr << " has parents" << endl;
                    for (int i = 0; i < parents[cr].size(); i++)
                        cerr << "  - " << logic.getPterm(parents[cr][i]).getId() << endl;
#endif
                }
            }
            qu[ci].done = true;
        }
        if (unprocessed_children)
            continue;
        assert(!occs.contains(qu[ci].x));
        occs.insert(qu[ci].x, 1);
        terms.push(qu[ci].x);
        qu.pop();
    }

#ifdef ENABLE_SHARING_BUG
    fc = rewriteMaxArity(fc.getRoot(), occs);
#else

    vec<PtChild> and_roots;
    vec<PtChild> or_roots;
    Map<PTRef,PTRef,PTRefHash,Equal<PTRef> > parent;

    PTRef root = fc.getRoot();

    vec<PtChild> mainq;
    mainq.push(PtChild(root, PTRef_Undef, -1));
    parent.insert(root, PTRef_Undef);
    Map<PTRef, PTRef, PTRefHash> processed; // To reuse duplicate terms

    while (mainq.size() != 0) {
        // Find the and- or or-roots
        while (mainq.size() != 0) {
            PtChild ptc = mainq.last(); mainq.pop();
            Pterm& t = logic.getPterm(ptc.tr);
            if (logic.isAnd(ptc.tr))
                and_roots.push(ptc);
            else if (logic.isOr(ptc.tr))
                or_roots.push(ptc);

            else
                for (int i = t.size()-1; i >= 0; i--)
//                for (int i = 0; i < t.size(); i++)
                    if (!parent.contains(t[i])) {
                        assert(logic.getPterm(ptc.tr).size() > i);
                        mainq.push(PtChild(t[i], ptc.tr, i));
                        parent.insert(t[i], ptc.tr);
                    }
        }

        // Process starting from them
        while (and_roots.size() + or_roots.size() != 0) {
            if (and_roots.size() != 0) {
                bool changed = false;  // Did we find ands to collapse
                vec<PTRef> args;
                vec<PTRef> queue;
                vec<PtChild> new_ors;
                vec<PtChild> new_ands;
                vec<PtChild> new_mains;

                PtChild and_root = and_roots.last(); and_roots.pop();

#ifdef SIMPLIFY_DEBUG
                if (and_root.parent != PTRef_Undef)
                    assert(logic.getPterm(and_root.parent).size() > and_root.pos);
//                cerr << "and root: " << logic.printTerm(and_root.tr) << endl;
#endif
                Pterm& and_root_t = logic.getPterm(and_root.tr);
 //               for (int i = 0; i < and_root_t.size(); i++)
                for (int i = and_root_t.size()-1; i >= 0; i--)
                    queue.push(and_root_t[i]);

                while (queue.size() != 0) {
                    PTRef tr = queue.last(); queue.pop();
                    assert(tr != and_root.tr);
                    Pterm& t = logic.getPterm(tr);
                    if (logic.isAnd(tr)) {
                        if (occs[tr] > 1) {
                            // This tr is used elsewhere.
                            // Open it once, store its opened version and
                            // use the opened term next time it is seen.
                            if (processed.contains(tr)) {
                                args.push(processed[tr]);
                                changed = true;
                            } else { // The new and root
                                args.push(tr);
                            }
#ifdef SIMPLIFY_DEBUG
                            cerr << " Using shared structure (" << occs[tr];
                            PTRef tmp_tr;
                            if (processed.contains(tr))
                                tmp_tr = processed[tr];
                            else
                                tmp_tr = tr;
                            char* name = logic.printTerm(tmp_tr);
                            cerr << " * " << name << endl;
                            ::free(name);
#endif
                        } else {
                            changed = true; // We need a new and
                            for (int i = t.size()-1; i >= 0; i--)
//                            for (int i = 0; i < t.size(); i++)
                                queue.push(t[i]);
                        }
                    } else
                        args.push(tr);
                }

                PTRef par_tr;

                // Do not duplicate if nothing changed
                if (changed) {
                    par_tr = logic.mkAnd(args);
                    for (int i = 0; i < args.size(); i++) {
                        if (logic.isAnd(args[i]) && occs[args[i]] < 2)
                            and_roots.push(PtChild(args[i], par_tr, i));
                        else if (logic.isOr(args[i]))
                            or_roots.push(PtChild(args[i], par_tr, i));
                        else
                            mainq.push(PtChild(args[i], par_tr, i));
                    }
                    if (occs.contains(par_tr))
                        occs[par_tr]++;
                    else
                        occs.insert(par_tr, 1);
                } else
                    par_tr = and_root.tr;

                processed.insert(and_root.tr, par_tr);

                if (and_root.parent != PTRef_Undef) {
//                    assert(logic.getPterm(and_root.parent).size() > and_root.pos);
                    logic.getPterm(and_root.parent)[and_root.pos] = par_tr;
#ifdef SIMPLIFY_DEBUG
                    cerr << logic.printTerm(and_root.parent) << endl;
#endif
                }
                else
                    fc.setRoot(par_tr);
#ifdef SIMPLIFY_DEBUG
//                cerr << " => " << logic.printTerm(par_tr) << endl;
#endif
            }

            if (or_roots.size() != 0) {
                bool changed = false;  // Did we find ors to collapse
                vec<PTRef> args;
                vec<PTRef> queue;
                vec<PtChild> new_ors;
                vec<PtChild> new_ands;
                vec<PtChild> new_mains;

                PtChild or_root = or_roots.last(); or_roots.pop();

#ifdef SIMPLIFY_DEBUG
                if (or_root.parent != PTRef_Undef)
                    assert(logic.getPterm(or_root.parent).size() > or_root.pos);
//                cerr << "or root: " << logic.printTerm(or_root.tr) << endl;
#endif
                Pterm& or_root_t = logic.getPterm(or_root.tr);
//                for (int i = 0; i < or_root_t.size(); i++)
                for (int i = or_root_t.size()-1; i >= 0; i--)
                    queue.push(or_root_t[i]);

                while (queue.size() != 0) {
                    PTRef tr = queue.last(); queue.pop();
                    assert(tr != or_root.tr);
                    Pterm& t = logic.getPterm(tr);
                    if (logic.isOr(tr)) { // We need a new or
                        if (occs[tr] > 1) {
                            // This tr is used elsewhere.
                            // Open it once, store its opened version and
                            // use the opened term next time it is seen.
                            if (processed.contains(tr)) {
                                args.push(processed[tr]);
                                changed = true; // We need a new or
                            } else { // The new or root
                                args.push(tr);
                            }
#ifdef SIMPLIFY_DEBUG
                            cerr << " Using shared structure (" << occs[tr];
                            PTRef tmp_tr;
                            if (processed.contains(tr))
                                tmp_tr = processed[tr];
                            else
                                tmp_tr = tr;
                            char* name = logic.printTerm(tmp_tr);
                            cerr << " * " << name << endl;
                            ::free(name);
#endif
                        } else {
                            changed = true; // We need a new or
                            for (int i = t.size()-1; i >= 0; i--)
//                            for (int i = 0; i < t.size(); i++)
                                queue.push(t[i]);
                        }
                    } else
                        args.push(tr);
                }

                PTRef par_tr;

                // Do not duplicate if nothing changed
                if (changed) {
                    par_tr = logic.mkOr(args);
                    for (int i = 0; i < args.size(); i++) {
                        if (logic.isOr(args[i]) && occs[args[i]] < 2)
                            or_roots.push(PtChild(args[i], par_tr, i));
                        else if (logic.isAnd(args[i]))
                            and_roots.push(PtChild(args[i], par_tr, i));
                        else
                            mainq.push(PtChild(args[i], par_tr, i));
                    }
                    if (occs.contains(par_tr))
                        occs[par_tr]++;
                    else
                        occs.insert(par_tr, 1);
                } else
                    par_tr = or_root.tr;

                processed.insert(or_root.tr, par_tr);

                if (or_root.parent != PTRef_Undef) {
//                    assert(logic.getPterm(or_root.parent).size() > or_root.pos);
                    logic.getPterm(or_root.parent)[or_root.pos] = par_tr;
#ifdef SIMPLIFY_DEBUG
                    cerr << logic.printTerm(or_root.parent) << endl;
#endif
                }
                else
                    fc.setRoot(par_tr);

#ifdef SIMPLIFY_DEBUG
//                cerr << " => " << logic.printTerm(par_tr) << endl;
#endif
            }
        }
    }
#endif
    return fc;
}

//
// Merge terms with shared signatures in egraph representation and remove redundancies in
// equalities and disequalities
//
MainSolver::FContainer MainSolver::simplifyEqualities(vec<PtChild>& terms)
{
#ifdef SIMPLIFY_DEBUG
    for (int i = 0; i < terms.size(); i++) {
        PtChild& ptc = terms[i];
        // XXX The terms in here might have invalid symbols for some reason.
//        assert(logic.hasSym(logic.getPterm(ptc.tr).symb()));
    }
#endif
    PTRef root = terms[terms.size()-1].tr;
    for (int i = 0; i < terms.size(); i++) {
        PtChild& ptc = terms[i];
        PTRef tr = ptc.tr;
        if (logic.isTheoryTerm(tr) && logic.getTerm_true() != tr && logic.getTerm_false() != tr) {
            if (logic.isEquality(tr)) {
                if (uf_solver.simplifyEquality(ptc, true)) {
                    // the root of the formula is trivially true
                    root = logic.getTerm_true();
                    break;
                }

#ifdef SIMPLIFY_DEBUG
                if (ptc.parent != PTRef_Undef && tr != logic.getPterm(ptc.parent)[ptc.pos]) {
                    cerr << "Simplified equality " << logic.printTerm(tr) << endl;
                    cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
                }
#endif
            }
            else if (logic.isDisequality(tr)) {
//                cerr << "Simplifying disequality " << logic.printTerm(tr) << endl;
                uf_solver.simplifyDisequality(ptc);
//                cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
            }
            uf_solver.declareTerm(ptc);
        }
    }
    return FContainer(root);
}

//
// Read the solver state from a file and store it to the main solver
//
bool MainSolver::readSolverState(const char* file, char** msg)
{
    CnfState cs;
    int fd = open(file, O_RDONLY);
    if (fd == -1) {
        *msg = strerror(errno);
        return false;
    }

    off_t size;
    int res;
    struct stat stat_buf;
    res = fstat(fd, &stat_buf);
    if (res == -1) {
        *msg = strerror(errno);
        return false;
    }
    size = stat_buf.st_size;

    // Allocate space for the contents and a terminating '\0'.
    int* contents = (int*)malloc(size+1);
    res = read(fd, contents, size);
    if (res == -1) {
        *msg = strerror(errno);
        return false;
    }

#ifdef USE_GZ
    int* contents_uncompressed;
    int sz_out;
    if (decompress_buf(contents, contents_uncompressed, size, sz_out) != Z_OK) {
        asprintf(msg, "decompression error");
        return false;
    }
    free(contents);
    contents = contents_uncompressed;
    size = sz_out;
    assert(contents[0] == sz_out);
#endif
    ((char*)contents)[size] = '\0'; // Add the terminating '\0'

    int map_offs = contents[map_offs_idx];
    int cnf_offs = contents[cnf_offs_idx];
    int termstore_offs = contents[termstore_offs_idx];
    int symstore_offs = contents[symstore_offs_idx];
    int idstore_offs = contents[idstore_offs_idx];
    int sortstore_offs = contents[sortstore_offs_idx];
    int logicstore_offs = contents[logicstore_offs_idx];

#ifdef VERBOSE_FOPS
    cerr << "Reading the map" << endl;
#endif
    for (int i = 0; i < contents[map_offs]-1; i++) {
       PTRef tr;
       tr.x = contents[i+map_offs+1];
       cs.addToMap({i, tr});
#ifdef VERBOSE_FOPS
       cerr << "  Var " << i << " maps to PTRef " << tr.x << endl;
#endif
    }

#ifdef VERBOSE_FOPS
    cerr << "Reading IdentifierStore" << endl;
#endif
    int idstore_sz = contents[idstore_offs];
    int* idstore_buf = (int*)malloc(contents[idstore_offs]*sizeof(int));
    for (int i = 0; i < idstore_sz; i++)
        idstore_buf[i] = contents[idstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Identifier store size in words is " << idstore_sz << endl;
    cerr << "Reading sort store" << endl;
#endif
    int sortstore_sz = contents[sortstore_offs];
    int* sortstore_buf = (int*)malloc(contents[sortstore_offs]*sizeof(int));
    for (int i = 0; i < sortstore_sz; i++)
        sortstore_buf[i] = contents[sortstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Sort store size in words is " << sortstore_sz << endl;
    cerr << "Reading symstore" << endl;
#endif
    int symstore_sz = contents[symstore_offs];
    int *symstore_buf = (int*)malloc(contents[symstore_offs]*sizeof(int));
    for (int i = 0; i < symstore_sz; i++)
        symstore_buf[i] = contents[symstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Symstore size is " << symstore_sz << endl;
    cerr << "Reading termstore" << endl;
#endif
    int termstore_sz = contents[termstore_offs];
    int *termstore_buf = (int*)malloc(contents[termstore_offs]*sizeof(int));
    for (int i = 0; i < termstore_sz; i++)
        termstore_buf[i] = contents[termstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Termstore size is " << termstore_sz << endl;
#endif

    int logicstore_sz = contents[logicstore_offs];
    int *logicstore_buf = (int*)malloc(contents[logicstore_offs]*sizeof(int));
    for (int i = 0; i < logicstore_sz; i++)
        logicstore_buf[i] = contents[logicstore_offs+i];

    logic.deserializeTermSystem(termstore_buf, symstore_buf, idstore_buf, sortstore_buf, logicstore_buf);
    free(termstore_buf);
    free(symstore_buf);
    free(idstore_buf);
    free(sortstore_buf);
    free(logicstore_buf);

    char* tmp_cnf;
    asprintf(&tmp_cnf, "%s", (char*)(contents + cnf_offs));
    cs.setCnf(tmp_cnf);
    const vec<VarPtPair>& map = cs.getMap();
#ifdef VERBOSE_FOPS
    cerr << "The cnf is" << endl;
    cerr << cs.getCnf() << endl;
    cerr << "The terms are" << endl;
    for (int i = 0; i < map.size(); i++) {
        char* tr_s = logic.printTerm(map[i].tr);
        cerr << "  " << tr_s << endl;
        free(tr_s);
    }
#endif

    for (int i = 0; i < map.size(); i++) {
        if (i >= sat_solver.nVars()) {
            int j = sat_solver.newVar();
            assert(j == i);
        }
        if (tmap.varToTerm.size() > i)
            assert(tmap.varToTerm[i] == map[i].tr);
        else
            tmap.varToTerm.push(map[i].tr);

        if (tmap.termToVar.contains(map[i].tr))
            assert(tmap.termToVar[map[i].tr] == i);
        else
            tmap.termToVar.insert(map[i].tr, i);
        if (tmap.varToTheorySymbol.size() > i)
            assert(tmap.varToTheorySymbol[i] == logic.getPterm(map[i].tr).symb());
        else {
            if (logic.isTheoryTerm(map[i].tr)) {
                tmap.varToTheorySymbol.push(logic.getPterm(map[i].tr).symb());
                sat_solver.setFrozen(i, true);
            }
            else tmap.varToTheorySymbol.push(SymRef_Undef);
        }
        uf_solver.declareTermTree(map[i].tr);
    }

#if defined(TERMS_HAVE_EXPLANATIONS)
    const vec<ERef>& ens = uf_solver.getEnodes();
    for (int i = 0; i < ens.size(); i++) {
        ERef er = ens[i];
        PTRef tr = uf_solver.ERefToTerm(er);
        Pterm& t = logic.getPterm(tr);
        t.setExpTimeStamp(0);
        assert(t.getExpReason() == PtAsgn_Undef);
        assert(t.getExpParent() == PTRef_Undef);
        assert(t.getExpRoot() == tr);
//        assert(t.getExpClassSize() == 1);
//        assert(t.getExpTimeStamp() == 0);
    }
#endif
    DimacsParser dp;
    dp.parse_DIMACS_main(cs.getCnf(), sat_solver);
    close(fd);
    free(contents);
    return true;
}

//
// Write the solver state to a partly binary file (cnf is in clear text
// and written last).  Output format looks like this:
//
// +--+-----+-----------+-------------+-------+--------------+---------------+-----------+
// |sz|map_offs|tstore_offs|symstore_offs|id_offs|sortstore_offs|logicstore_offs|cnf_offs|
// +--------+-----------+-------------+-------+--------------+---------------+-----------+
// |map_sz              | <map data>                                                     |
// +--------------------+----------------------------------------------------------------+
// |tstore_sz           | <tstore data>                                                  |
// +--------------------+----------------------------------------------------------------+
// |symstore_sz         | <symstore data>                                                |
// +--------------------+----------------------------------------------------------------+
// |idstore_sz          | <idstore data>                                                 |
// +--------------------+----------------------------------------------------------------+
// |sortstore_sz        | <sortstore data>                                               |
// +--------------------+----------------------------------------------------------------+
// |logicstore_sz       | <logicstore data>                                              |
// +--------------------+----------------------------------------------------------------+
// |<cnf data>                                                                           |
// +-------------------------------------------------------------------------------------+
//
// The sizes include the storage of the size itself.  All sizes with the
// exception of sz are given in number of integers.  sz is given in
// number of characters.
//
//

bool MainSolver::writeState(const char* file, CnfState& cs, char** msg)
{
    int fd = open(file, O_WRONLY | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP);
    if (fd == -1) {
        *msg = strerror(errno);
        return false;
    }
    // Reset, ok.

#ifdef VERBOSE_FOPS
    cerr << "Trying to write solver state" << endl;
    cerr << "Cnf: " << endl;
    cerr << cs.getCnf() << endl;
    cerr << "The terms are" << endl;
    for (int i = 0; i < cs.getMap().size(); i++) {
        char* tr_s = logic.printTerm(cs.getMap()[i].tr);
        cerr << "  " << tr_s << endl;
        free(tr_s);
    }

#endif

    int* termstore_buf;
    int* symstore_buf;
    int* idstore_buf;
    int* sortstore_buf;
    int* logicstore_buf;

    // Clear the timestamp for explanations!
    const vec<ERef>& ens = uf_solver.getEnodes();
    for (int i = 0; i < ens.size(); i++) {
        ERef er = ens[i];
        PTRef tr = uf_solver.ERefToTerm(er);
        Pterm& t = logic.getPterm(tr);
#ifdef TERMS_HAVE_EXPLANATIONS
        t.setExpTimeStamp(0);
        t.setExpReason(PtAsgn(PTRef_Undef, l_Undef));
        t.setExpParent(PTRef_Undef);
        t.setExpRoot(tr);
#endif
    }

    logic.serializeTermSystem(termstore_buf, symstore_buf, idstore_buf, sortstore_buf, logicstore_buf);

    // All stores contain their sizes, hence the minimum size of 1

    int idstore_sz    = idstore_buf[0];
    int sortstore_sz  = sortstore_buf[0];
    int map_sz        = cs.getMap().size()+1;
    int symstore_sz   = symstore_buf[0];
    int termstore_sz  = termstore_buf[0];
    int logicstore_sz = logicstore_buf[0];

    int hdr_sz = 8; // The offsets
    // allocate space for the map, the cnf, the offset indices and the
    // sizes
    int buf_sz = (termstore_sz + symstore_sz + idstore_sz + sortstore_sz + map_sz + logicstore_sz)*sizeof(int)
                 + (strlen(cs.getCnf())+1) + hdr_sz*sizeof(int);
#ifdef VERBOSE_FOPS
    cerr << "Mallocing " << buf_sz << " bytes for the buffer" << endl;
    cerr << "The cnf is " << strlen(cs.getCnf())+1 << " bytes" << endl;
    cerr << "The map is " << map_sz * sizeof(int) << " bytes" << endl;
    cerr << "The termstore is " << termstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The symstore is " << symstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The id store is " << idstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The sortstore is " << sortstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The header is " << hdr_sz*sizeof(int) << " bytes" << endl;
#endif
    int* buf = (int*)malloc(buf_sz);

    buf[map_offs_idx]        = cnf_offs_idx+1;
    buf[termstore_offs_idx]  = buf[map_offs_idx]+map_sz;
    buf[symstore_offs_idx]   = buf[termstore_offs_idx] + termstore_sz;
    buf[idstore_offs_idx]    = buf[symstore_offs_idx] + symstore_sz;
    buf[sortstore_offs_idx]  = buf[idstore_offs_idx] + idstore_sz;
    buf[logicstore_offs_idx] = buf[sortstore_offs_idx] + sortstore_sz;
    buf[cnf_offs_idx]        = buf[logicstore_offs_idx]+logicstore_sz;


    buf[buf[map_offs_idx]]          = map_sz;

    // These will be replaced by the actual buffers
    buf[buf[termstore_offs_idx]]    = termstore_sz;
    buf[buf[symstore_offs_idx]]     = symstore_sz;

#ifdef VERBOSE_FOPS
    cerr << "Map:" << endl;
#endif
    for (int i = 0; i < cs.getMap().size(); i++) {
#ifdef VERBOSE_FOPS
        cerr << "  Var " << i << " maps to " << cs.getMap()[i].tr.x << endl;
        cerr << "  Writing it to idx " << buf[map_offs_idx]+i+1 << endl;
#endif
        buf[buf[map_offs_idx]+i+1] = cs.getMap()[i].tr.x;
    }
#ifdef VERBOSE_FOPS
    cerr << "Will write cnf to index " << buf[cnf_offs_idx] << endl;
#endif
    char* cnf_buf = (char*) (&buf[buf[cnf_offs_idx]]);
    int i;
    const char* in_cnf = cs.getCnf();
    for (i = 0; in_cnf[i] != 0; i++)
        cnf_buf[i] = in_cnf[i];
    cnf_buf[i] = '\0';

    for (i = 0; i < idstore_sz; i++)
        buf[buf[idstore_offs_idx]+i] = idstore_buf[i];

    free(idstore_buf);

    for (i = 0; i < sortstore_sz; i++)
        buf[buf[sortstore_offs_idx]+i] = sortstore_buf[i];

    for (int i = 0; i < symstore_sz; i++)
        buf[buf[symstore_offs_idx]+i] = symstore_buf[i];

    for (int i = 0; i < termstore_sz; i++)
        buf[buf[termstore_offs_idx]+i] = termstore_buf[i];

    for (int i = 0; i < logicstore_sz; i++)
        buf[buf[logicstore_offs_idx]+i] = logicstore_buf[i];

#ifdef VERBOSE_FOPS
    cerr << "Map offset read from buf idx " << map_offs_idx << endl;
    cerr << "Map starts at word " << buf[map_offs_idx] << endl;
    cerr << "Map size is " << buf[buf[map_offs_idx]] << endl;

    cerr << "tstore offset read from buf idx " << termstore_offs_idx << endl;
    cerr << "tstore starts at word " << buf[termstore_offs_idx] << endl;
    cerr << "tstore size is " << buf[buf[termstore_offs_idx]] << endl;

    cerr << "symstore offset read from buf idx " << symstore_offs_idx << endl;
    cerr << "symstore starts at word " << buf[symstore_offs_idx] << endl;
    cerr << "symstore size is " << buf[buf[symstore_offs_idx]] << endl;

    cerr << "idstore offset read from buf idx " << idstore_offs_idx << endl;
    cerr << "idstore starts at word " << buf[idstore_offs_idx] << endl;
    cerr << "idstore size is " << buf[buf[idstore_offs_idx]] << endl;

    cerr << "sortstore offset read from buf idx " << sortstore_offs_idx << endl;
    cerr << "sortstore starts at word " << buf[sortstore_offs_idx] << endl;
    cerr << "sortstore size is " << buf[buf[sortstore_offs_idx]] << endl;
#endif
#ifdef PEDANTIC_DEBUG
    SMTConfig new_config;
    SymStore new_symstore;
    IdentifierStore new_idstore;
    SStore new_sortstore(new_config, new_idstore);
    PtStore new_tstore(new_symstore, new_sortstore);

    new_symstore.deserializeSymbols(&buf[buf[symstore_offs_idx]]);
    logic.compareSymStore(new_symstore);
    new_idstore.deserializeIdentifiers(&buf[buf[idstore_offs_idx]]);
    logic.compareIdStore(new_idstore);
//    logic.compareTermStore(new_tstore);
    new_tstore.deserializeTerms(&buf[buf[termstore_offs_idx]]);
//    Logic new_logic(new_config, new_idstore, new_sortstore, new_symstore, new_tstore);
//    TermMapper new_tmap(new_logic);
//    Egraph new_uf_solver(new_config, new_sortstore, new_symstore, new_tstore, new_logic, new_tmap);
//    THandler new_thandler(new_uf_solver, new_config, new_tmap, new_logic);
//    SimpSMTSolver new_sat_solver(new_config, new_thandler);

    for (int i = 0; i < cs.getMap().size(); i++) {
        Pterm& my_t = logic.getPterm(cs.getMap()[i].tr);
        Pterm& other_t = new_tstore[cs.getMap()[i].tr];
        my_t.compare(other_t);
    }

#endif
    // Write the size in characters
    buf[0] = buf_sz - 1;
#ifdef USE_GZ
    // Compress the buffer and update the write info accordingly
    int* buf_out;
    int rval = compress_buf(buf, buf_out, buf_sz-1, buf_sz);
    if (rval != Z_OK) {
        asprintf(msg, "compression error");
        close(fd);
        return false;
    }
    int write_sz = buf_sz;
#else
    int write_sz = buf_sz - 1;
#endif

    int res = write(fd, buf_out, write_sz);
    if (res == -1) {
        *msg = strerror(errno);
        return false;
    } else if (res != write_sz) {
        asprintf(msg, "Not all data was written.  Out of space?");
        close(fd);
        return false;
    }

#ifdef VERBOSE_FOPS
    cerr << "Printed " << res  << " bytes" << endl;
#endif
    free(buf);
    close(fd);
    return true;
}

bool MainSolver::writeSolverState(const char* file, char** msg)
{
    CnfState cs;
    ts.getVarMapping(cs);
    ts.getSolverState(cs);
    return writeState(file, cs, msg);
}

bool MainSolver::writeSolverSplits(const char* file, char** msg)
{
    for (int i = 0; i < sat_solver.splits.size(); i++) { // free name!
        char* name;
        asprintf(&name, "%s-%02d.osmt2", file, i);
        CnfState cs;
        ts.getVarMapping(cs);
        sat_solver.splits[i].cnfToString(cs);
        if (!writeState(name, cs, msg)) {
            free(name);
            return false;
        }
        free(name);
    }
    return true;
}

