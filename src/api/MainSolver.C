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

namespace opensmt { extern bool stop; }
#include "symmetry/Symmetry.h"

int PushFrame::id_counter = 0;

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

sstat
MainSolver::push(PTRef root)
{
    formulas.push();
    char* msg;
    sstat res = insertFormula(root, &msg);
    if (res == s_Error)
        printf("%s\n", msg);
    return res;
}

sstat
MainSolver::insertFormula(PTRef root, char** msg)
{
    if (logic.getSortRef(root) != logic.getSort_bool())
    {
        asprintf(msg, "Top-level assertion sort must be %s, got %s",
                 Logic::s_sort_bool, logic.getSortName(logic.getSortRef(root)));
        return s_Error;
    }
    logic.conjoinItes(root, root);
    char* err_msg = NULL;
    if (!logic.assignPartition(root, &err_msg))
        opensmt_error("Could not assign partition"); 
#ifdef PRODUCE_PROOF
    logic.setIPartitionsIte(root);
#endif
    formulas.last().push(root);
    return s_Undef;
}

sstat MainSolver::simplifyFormulas(char** err_msg) {
    if (binary_init)
        return s_Undef;

    status = s_Undef;
    // Think of something here to enable incrementality...
    if (!ts.solverEmpty()) {
        asprintf(err_msg, "Solver already contains a simplified problem.  Cannot continue for now");
        return s_Error;
    }

    vec<PTRef> coll_f;
    for (int i = simplified_until; i < formulas.size(); i++) {
        bool res = getTheory().simplify(formulas, i);
        simplified_until = i+1;
        PTRef root = formulas[i].root;
        if (logic.isTrue(root)) return status = s_True;
        else if (logic.isFalse(root)) return status = s_False;

        FContainer fc(root);

        // Optimize the dag for cnfization
        Map<PTRef,int,PTRefHash> PTRefToIncoming;
        if (logic.isBooleanOperator(fc.getRoot())) {
#ifdef FLATTEN_DEBUG
            printf("Flattening the formula %s\n", logic.printTerm(fc.getRoot()));
#endif
            computeIncomingEdges(fc.getRoot(), PTRefToIncoming);
            PTRef flat_root = rewriteMaxArity(fc.getRoot(), PTRefToIncoming);
            fc.setRoot(flat_root);
#ifdef FLATTEN_DEBUG
            printf("Got the formula %s\n", logic.printTerm(fc.getRoot()));
#endif
        }

        root_instance = fc;
        status = giveToSolver(fc.getRoot(), formulas[i].getId());
    }
    return status;
}

void MainSolver::expandItes(FContainer& fc, vec<PtChild>& terms)
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

void MainSolver::computeIncomingEdges(PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    assert(tr != PTRef_Undef);
    vec<pi*> unprocessed_ptrefs;
    unprocessed_ptrefs.push(new pi(tr));
    while (unprocessed_ptrefs.size() > 0) {
        pi* pi_ptr = unprocessed_ptrefs.last();
        if (PTRefToIncoming.has(pi_ptr->x)) {
            PTRefToIncoming[pi_ptr->x]++;
            unprocessed_ptrefs.pop();
            delete pi_ptr;
            continue;
        }
        bool unprocessed_children = false;
        if (logic.isBooleanOperator(pi_ptr->x) && pi_ptr->done == false) {
            Pterm& t = logic.getPterm(pi_ptr->x);
            for (int i = 0; i < t.size(); i++) {
                // push only unprocessed Boolean operators
                if (!PTRefToIncoming.has(t[i])) {
                    unprocessed_ptrefs.push(new pi(t[i]));
                    unprocessed_children = true;
                } else {
                    PTRefToIncoming[t[i]]++;
                }
            }
            pi_ptr->done = true;
        }
        if (unprocessed_children)
            continue;

        unprocessed_ptrefs.pop();
        // All descendants of pi_ptr->x are processed
        assert(logic.isBooleanOperator(pi_ptr->x) || logic.isAtom(pi_ptr->x));
        assert(!PTRefToIncoming.has(pi_ptr->x));
        PTRefToIncoming.insert(pi_ptr->x, 1);
        delete pi_ptr;
    }
}

PTRef MainSolver::rewriteMaxArity(PTRef root, Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    vec<PTRef> unprocessed_ptrefs;
    unprocessed_ptrefs.push(root);
    Map<PTRef,PTRef,PTRefHash> cache;

    while (unprocessed_ptrefs.size() > 0) {
        PTRef tr = unprocessed_ptrefs.last();
        if (cache.has(tr)) {
            unprocessed_ptrefs.pop();
            continue;
        }

        bool unprocessed_children = false;
        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            if (logic.isBooleanOperator(t[i]) && !cache.has(t[i])) {
                unprocessed_ptrefs.push(t[i]);
                unprocessed_children = true;
            }
            else if (logic.isAtom(t[i]))
                cache.insert(t[i], t[i]);
        }
        if (unprocessed_children)
            continue;

        unprocessed_ptrefs.pop();
        PTRef result = PTRef_Undef;
        assert(logic.isBooleanOperator(tr));

        if (logic.isAnd(tr) || logic.isOr(tr)) {
            result = mergePTRefArgs(tr, cache, PTRefToIncoming);
        } else {
            result = tr;
        }
        assert(result != PTRef_Undef);
        assert(!cache.has(tr));
        cache.insert(tr, result);
#ifdef PRODUCE_PROOF
        if(logic.isInterpolating())
        {
            if(logic.isAssertion(tr))
            {
                if(logic.isAnd(result))
                {
                    Pterm& ptm = logic.getPterm(result);
                    for(int i = 0; i < ptm.size(); ++i)
                        logic.setOriginalAssertion(ptm[i], tr);
                }
                //else //should the entire conjunction also be set? TODO
                logic.setOriginalAssertion(result, tr);
            }
        }
#endif
    }
    PTRef top_tr = cache[root];
    return top_tr;
}

PTRef MainSolver::mergePTRefArgs(PTRef tr, Map<PTRef,PTRef,PTRefHash>& cache, Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    assert(logic.isAnd(tr) || logic.isOr(tr));
    Pterm& t = logic.getPterm(tr);
    SymRef sr = t.symb();
    vec<PTRef> new_args;
    for (int i = 0; i < t.size(); i++) {
        PTRef subst = cache[t[i]];
        if (logic.getSymRef(t[i]) != sr) {
            new_args.push(subst);
            continue;
        }
        assert(PTRefToIncoming.has(t[i]));
        assert(PTRefToIncoming[t[i]] >= 1);
        if (PTRefToIncoming[t[i]] > 1) {
            new_args.push(subst);
            continue;
        }
        if (logic.getSymRef(subst) == sr) {
            Pterm& substs_t = logic.getPterm(subst);
            for (int j = 0; j < substs_t.size(); j++)
                new_args.push(substs_t[j]);
        } else
            new_args.push(subst);
    }
    if (sr == logic.getSym_and())
        return logic.mkAnd(new_args);
    else
        return logic.mkOr(new_args);
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
                if (logic.simplifyEquality(ptc, true)) {
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
                logic.simplifyDisequality(ptc);
//                cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
            }
//            uf_solver.declareTerm(ptc);
        }
    }
    return FContainer(root);
}

ValPair MainSolver::getValue(PTRef tr) const
{
    if (logic.hasSortBool(tr)) {
        lbool val = ts.getTermValue(tr);
        return ValPair(tr, val == l_True ? "true" : (val == l_False ? "false" : "unknown"));
    } else {
        return thandler.getValue(tr);
    }
    return ValPair();
}

void MainSolver::getValues(const vec<PTRef>& trs, vec<ValPair>& vals) const
{
    vals.clear();
    for (int i = 0; i < trs.size(); i++)
    {
        PTRef tr = trs[i];
        vals.push(getValue(tr));
    }
}


//
// Read the solver state from a file and store it to the main solver
//
bool MainSolver::readSolverState(const char* file, char** msg)
{
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
    int *contents = (int *) malloc((size_t)size);
    res = read(fd, contents, size);
    if (res == -1) {
        *msg = strerror(errno);
        return false;
    }
    close(fd);

    bool r = readSolverState(contents, (int)size, true, msg);
    free(contents);

    return r;
}

//
// Read the solver state from a buffer
//
bool MainSolver::readSolverState(int* buf, int buf_sz, bool compressed, char **msg)
{

    if(compressed) {
#ifdef USE_GZ
        int* contents_uncompressed;
        int rval = decompress_buf(buf, contents_uncompressed, buf_sz, buf_sz);
        if (rval != Z_OK) {
            asprintf(msg, "decompression error");
            return false;
        }
        buf = contents_uncompressed;
        assert(buf[0] == buf_sz);
#endif
    }

    CnfState cs;
    int map_offs = buf[map_offs_idx];
    int cnf_offs = buf[cnf_offs_idx];
    int termstore_offs = buf[termstore_offs_idx];
    int symstore_offs = buf[symstore_offs_idx];
    int idstore_offs = buf[idstore_offs_idx];
    int sortstore_offs = buf[sortstore_offs_idx];
    int logicstore_offs = buf[logicstore_offs_idx];

#ifdef VERBOSE_FOPS
    cerr << "Reading the map" << endl;
#endif
    for (int i = 0; i < buf[map_offs]-1; i++) {
        PTRef tr;
        tr.x = buf[i+map_offs+1];
        cs.addToMap({i, tr});
#ifdef VERBOSE_FOPS
        cerr << "  Var " << i << " maps to PTRef " << tr.x << endl;
#endif
    }

#ifdef VERBOSE_FOPS
    cerr << "Reading IdentifierStore" << endl;
#endif
    int idstore_sz = buf[idstore_offs];
    int* idstore_buf = (int*)malloc(buf[idstore_offs]*sizeof(int));
    for (int i = 0; i < idstore_sz; i++)
        idstore_buf[i] = buf[idstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Identifier store size in words is " << idstore_sz << endl;
    cerr << "Reading sort store" << endl;
#endif
    int sortstore_sz = buf[sortstore_offs];
    int* sortstore_buf = (int*)malloc(buf[sortstore_offs]*sizeof(int));
    for (int i = 0; i < sortstore_sz; i++)
        sortstore_buf[i] = buf[sortstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Sort store size in words is " << sortstore_sz << endl;
    cerr << "Reading symstore" << endl;
#endif
    int symstore_sz = buf[symstore_offs];
    int *symstore_buf = (int*)malloc(buf[symstore_offs]*sizeof(int));
    for (int i = 0; i < symstore_sz; i++)
        symstore_buf[i] = buf[symstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Symstore size is " << symstore_sz << endl;
    cerr << "Reading termstore" << endl;
#endif
    int termstore_sz = buf[termstore_offs];
    int *termstore_buf = (int*)malloc(buf[termstore_offs]*sizeof(int));
    for (int i = 0; i < termstore_sz; i++)
        termstore_buf[i] = buf[termstore_offs+i];
#ifdef VERBOSE_FOPS
    cerr << "  Termstore size is " << termstore_sz << endl;
#endif

    int logicstore_sz = buf[logicstore_offs];
    int *logicstore_buf = (int*)malloc(buf[logicstore_offs]*sizeof(int));
    for (int i = 0; i < logicstore_sz; i++)
        logicstore_buf[i] = buf[logicstore_offs+i];

    char* tmp_cnf;
    asprintf(&tmp_cnf, "%s", (char*)(buf + cnf_offs));
    cs.setCnf(tmp_cnf);

#ifdef VERBOSE_FOPS
    cerr << "The cnf is" << endl;
    cerr << cs.getCnf() << endl;

//    cerr << "The terms are" << endl;
//    for (int i = 0; i < map.size(); i++) {
//        char* tr_s = logic.printTerm(map[i].tr);
//        cerr << "  " << tr_s << endl;
//        free(tr_s);
//    }
#endif

    deserializeSolver(termstore_buf, symstore_buf, idstore_buf, sortstore_buf, logicstore_buf, cs);

//    logic.deserializeTermSystem(termstore_buf, symstore_buf, idstore_buf, sortstore_buf, logicstore_buf);
    free(termstore_buf);
    free(symstore_buf);
    free(idstore_buf);
    free(sortstore_buf);
    free(logicstore_buf);

    if(compressed) {
#ifdef USE_GZ
        free(buf);
#endif
    }

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

    int* buf;
    int write_sz;
    if(!writeState(buf, write_sz, true, cs, msg)) {
        return false;
    }

    int res = write(fd, buf, write_sz);
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


// It never returns false. in the future if that will happen
// make sure to free contents before return.
bool MainSolver::writeState(int* &buf, int &buf_sz, bool compress, CnfState& cs, char** msg)
{

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
    for (PtermIter it = logic.getPtermIter(); *it != PTRef_Undef; ++it) {
        Pterm& t = logic.getPterm(*it);
#ifdef TERMS_HAVE_EXPLANATIONS
        t.setExpTimeStamp(0);
        t.setExpReason(PtAsgn(PTRef_Undef, l_Undef));
        t.setExpParent(PTRef_Undef);
        t.setExpRoot(*it);
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
    buf_sz = (int)((termstore_sz + symstore_sz + idstore_sz + sortstore_sz + map_sz + logicstore_sz)*sizeof(int)
                 + (strlen(cs.getCnf())+1) + hdr_sz*sizeof(int));
#ifdef VERBOSE_FOPS
    cerr << "Mallocing " << *size << " bytes for the buffer" << endl;
    cerr << "The cnf is " << strlen(cs.getCnf())+1 << " bytes" << endl;
    cerr << "The map is " << map_sz * sizeof(int) << " bytes" << endl;
    cerr << "The termstore is " << termstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The symstore is " << symstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The id store is " << idstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The sortstore is " << sortstore_sz * sizeof(int) << " bytes" << endl;
    cerr << "The header is " << hdr_sz*sizeof(int) << " bytes" << endl;
#endif
    buf = (int *)malloc(buf_sz);

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
    free(sortstore_buf);

    for (int i = 0; i < symstore_sz; i++)
        buf[buf[symstore_offs_idx]+i] = symstore_buf[i];
    free(symstore_buf);

    for (int i = 0; i < termstore_sz; i++)
        buf[buf[termstore_offs_idx]+i] = termstore_buf[i];
    free(termstore_buf);

    for (int i = 0; i < logicstore_sz; i++)
        buf[buf[logicstore_offs_idx]+i] = logicstore_buf[i];
    free(logicstore_buf);

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
    logic.compareTermStore(new_tstore);
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
    buf[0] = (int)buf_sz;

    if(compress) {
#ifdef USE_GZ
        int* buf_out;
        // Compress the buffer and update the write info accordingly
        int rval = compress_buf(buf, buf_out, buf_sz, buf_sz);
        free(buf);
        buf = buf_out;
        if (rval != Z_OK) {
            asprintf(msg, "compression error");
            return false;
        }
#endif
    }

    return true;
}

void MainSolver::deserializeSolver(const int* termstore_buf, const int* symstore_buf, const int* idstore_buf, const int* sortstore_buf, const int* logicstore_buf, CnfState& cs)
{
    logic.deserializeTermSystem(termstore_buf, symstore_buf, idstore_buf, sortstore_buf, logicstore_buf);

    const vec<VarPtPair>& map = cs.getMap();
    for (int i = 0; i < map.size(); i++) {
        if (i >= ts.solver.nVars()) {
            int j = ts.solver.newVar();
            assert(j == i);
        }
        if (tmap.nVars() > i)
            assert(tmap.varToPTRef(i) == map[i].tr);
        else {
            tmap.addBinding(i, map[i].tr);

            if (logic.isTheoryTerm(map[i].tr))
                ts.solver.setFrozen(i, true);
        }
    }
#if defined(TERMS_HAVE_EXPLANATIONS)
    for (PtermIter it = logic.getPtermIter(); *it != PTRef_Undef; ++it) {
        Pterm& t = logic.getPterm(*it);
        t.setExpTimeStamp(0);
        assert(t.getExpReason() == PtAsgn_Undef);
        assert(t.getExpParent() == PTRef_Undef);
        assert(t.getExpRoot() == *it);
    }
#endif
    DimacsParser dp;
    dp.parse_DIMACS_main(cs.getCnf(), ts.solver);

    binary_init = true;

    return;
}

bool MainSolver::writeSolverState(const char* file, char** msg)
{
    CnfState cs;
    ts.getVarMapping(cs);
    ts.getSolverState(cs);
    return writeState(file, cs, msg);
}

bool MainSolver::writeSolverState(int* &buf, int &buf_sz, bool compress, char** msg)
{
    CnfState cs;
    ts.getVarMapping(cs);
    ts.getSolverState(cs);
    return writeState(buf,buf_sz,compress, cs, msg);
}

void MainSolver::addToConj(vec<vec<PtAsgn> >& in, vec<PTRef>& out)
{
    for (int i = 0; i < in.size(); i++) {
        vec<PtAsgn>& constr = in[i];
        vec<PTRef> disj_vec;
        for (int k = 0; k < constr.size(); k++)
            disj_vec.push(constr[k].sgn == l_True ? constr[k].tr : logic.mkNot(constr[k].tr));
        out.push(logic.mkOr(disj_vec));
    }
}

bool MainSolver::writeSolverState_smtlib2(const char* file, char** msg)
{
    char* name;
    asprintf(&name, "%s.smt2", file);
    std::ofstream file_s;
    file_s.open(name);
    if (file_s.is_open()) {
        logic.dumpHeaderToFile(file_s);
        logic.dumpFormulaToFile(file_s, root_instance.getRoot());
        logic.dumpChecksatToFile(file_s);
        file_s.close();
    }
    else {
        asprintf(msg, "Failed to open file %s\n", name);
        free(name);
        return false;
    }
    free(name);
    return true;
}

bool MainSolver::writeSolverSplits_smtlib2(const char* file, char** msg)
{
    vec<SplitData>& splits = ts.solver.splits;
    for (int i = 0; i < splits.size(); i++) {
        vec<PTRef> conj_vec;
        vec<vec<PtAsgn> > constraints;
        splits[i].constraintsToPTRefs(constraints);
        addToConj(constraints, conj_vec);

        vec<vec<PtAsgn> > learnts;
        splits[i].learntsToPTRefs(learnts);
        addToConj(learnts, conj_vec);

        conj_vec.push(root_instance.getRoot());
        PTRef problem = logic.mkAnd(conj_vec);

        char* name;
        asprintf(&name, "%s-%02d.smt2", file, i);
        std::ofstream file;
        file.open(name);
        if (file.is_open()) {
            logic.dumpHeaderToFile(file);
            logic.dumpFormulaToFile(file, problem);
            logic.dumpChecksatToFile(file);
            file.close();
        }
        else {
            asprintf(msg, "Failed to open file %s\n", name);
            free(name);
            return false;
        }
        free(name);
    }
    return true;
}

bool MainSolver::writeSolverSplits(const char* file, char** msg)
{
    for (int i = 0; i < ts.solver.splits.size(); i++) {
        char* name;
        asprintf(&name, "%s-%02d.osmt2", file, i);
        CnfState cs;
        ts.getVarMapping(cs);
        ts.solver.splits[i].cnfToString(cs);

        if (!writeState(name, cs, msg)) {
            free(name);
            return false;
        }
        free(name);
    }
    return true;
}

bool MainSolver::writeSolverSplit(int s, int* &split, int &split_sz, bool compress, char** msg)
{
    assert(s < ts.solver.splits.size());

    CnfState cs;
    ts.getVarMapping(cs);
    ts.solver.splits[s].cnfToString(cs);
    if (!writeState(split, split_sz, compress, cs, msg)) {
        return false;
    }
    return true;
}

/*
bool MainSolver::writeSolverSplits(int** &splits, char** msg)
{
    splits = (int **)malloc(ts.solver.splits.size() * sizeof(int *));

    for (int i = 0; i < ts.solver.splits.size(); i++) {
        if (!writeSolverSplit(i, splits[i], msg)) {
            for (int j=0; j<i; j++){
                free(splits[j]);
            }
            free(splits);
            return false;
        }
    }
    return true;
}
*/

sstat MainSolver::check()
{
    sstat rval;
    rval = simplifyFormulas();
    if (rval != s_Undef)
        return rval;
    initialize();
    return solve();
}

sstat MainSolver::solve()
{
    int i, r, min;
    int pipefd[2];
    char buf[3];
    fd_set set;
    std::thread *threads;
    std::mutex mtx;
    sstat result;
    sstat *results;
    vec<int> *split_threads;

    if (config.parallel_threads && config.sat_split_type() == spt_lookahead)
        status = lookaheadSplit(getLog2Ceil(config.sat_split_num()));
    else {
        vec<int> en_frames;
        for (int i = 0; i < formulas.size(); i++)
            en_frames.push(formulas[i].getId());
        status = sstat(ts.solve(en_frames));
    }
    if (!(config.parallel_threads && status == s_Undef)) {
        if (status == s_True && config.produce_models())
            thandler.computeModel();
        return status;
    }

    opensmt::stop = false;

    if (pipe(pipefd) == -1) {
        cerr << "Pipe error";
        return status;
    }

    split_threads = new vec<int>[ts.solver.splits.size()];
    results = new sstat[ts.solver.splits.size()];
    for (i=0; i<ts.solver.splits.size(); i++) {
        results[i] = s_Undef;
    }

    std::mutex mtx1;

    // start the threads
    threads = new std::thread[config.parallel_threads];
    for (i=0; i<config.parallel_threads; i++) {
        this->parallel_solvers.push(NULL);
        r = i%ts.solver.splits.size();
        split_threads[r].push(i);
        threads[i] = std::thread(&MainSolver::solve_split,
                                 this,
                                 i,
                                 r,
                                 pipefd[1],
                                 &mtx
                                 );
    }
    
    // wait for messages from the threads
    while (1) {
        r=0;
        while (r<3) r+=::read(pipefd[0], &buf[r], 3-r);
        threads[(int)buf[0]].join();
        this->parallel_solvers[(int)buf[0]] = NULL;
        result = sstat((int)buf[2]);
        if (result == s_Undef || result == s_False){
            if (result == s_False) {
                cerr << "thread:" << (int)buf[0] << " split #" << (int)buf[1] << " unsat\n";
                results[(int)buf[1]] = s_False;
                for (i=0; i<split_threads[(int)buf[1]].size(); i++) {
                    r=split_threads[(int)buf[1]][i];
                    if (this->parallel_solvers[r]!=NULL) {
                        this->parallel_solvers[r]->stop();
                    }
                }
                // may empty split_threads[buf[1]] ...
            }
            r=-1;
            min = config.parallel_threads;
            for (i=0; i<ts.solver.splits.size(); i++) {
                if (results[i]!=s_Undef){
                    continue;
                }
                if (split_threads[i].size() <= min) {
                    r = i;
                    min = split_threads[i].size();
                }
            }
            if (r<0){
                break;
            }
            split_threads[r].push((int)buf[0]);
            threads[(int)buf[0]] = std::thread(&MainSolver::solve_split,
                                               this,
                                               (int)buf[0],
                                               r,
                                               pipefd[1],
                                               &mtx
                                               );
        }
        else {
            if (result == s_True) {
                cerr << "thread:" << (int)buf[0] << " split #" << (int)buf[1] << " sat\n";
            }
            else{
                cerr << "Error while solving split #" << (int)buf[1] << "\n";
            }
            break;
        }
    }

    opensmt::stop = true;

    for (i=0; i<config.parallel_threads; i++) {
        if (this->parallel_solvers[i]!=NULL) {
            this->parallel_solvers[i]->stop();
        }
    }
    for (i=0; i<config.parallel_threads; i++) {
        if (threads[i].joinable()) {
            threads[i].join();
        }
    }
    delete[] threads;
    delete[] results;
    delete[] split_threads;
    ::close(pipefd[0]);
    ::close(pipefd[1]);
    return status = result;
}

void MainSolver::solve_split(int i, int s, int wpipefd, std::mutex *mtx)
{
    char buf[3];

    buf[0] = (char)i;
    buf[1] = (char)s;

    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
    std::random_device rd;
    SMTConfig config;
    config.setRandomSeed(randuint(rd));

    Logic_t l = this->logic.getLogic();
    Theory* theory;
    if (l == QF_UF)
        theory = new UFTheory(config);
    else if (l == QF_LRA)
        theory = new LRATheory(config);
    else {
        cerr << "Unsupported logic" << endl;
        exit(1);
    }

    int* split;
    int split_sz;
    char* msg;
    sstat result = s_Undef;
    MainSolver* main_solver;
    if(!this->writeSolverSplit(s,split,split_sz,true,&msg)){
        std::cerr << "Thread " << i << ": " << msg << "\n";
        free(msg);
        goto done;
    }

    main_solver = new MainSolver(getTHandler(), config, new SimpSMTSolver(config, getTHandler()));
    main_solver->initialize();

    if (!main_solver->readSolverState(split,split_sz,true, &msg)) {
        std::cerr << "Thread " << i << ": " << msg << "\n";
        free(msg);
        goto done;
    }

    free(split);
    this->parallel_solvers[i] = main_solver;

    result = main_solver->simplifyFormulas(&msg);
    if (result != s_True && result != s_False)
        result = main_solver->solve();


    done:

    delete main_solver;
    main_solver = NULL;
    std::cout << "RISULTATO " << (int)result.getValue() << "\n";

    buf[2] = result.getValue();

    mtx->lock();
    ::write(wpipefd, buf, 3);
    mtx->unlock();
}
