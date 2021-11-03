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


#include "EnodeStore.h"
#include "Symbol.h"
#include "Logic.h"

EnodeStore::EnodeStore(Logic& l)
      : logic(l)
      , ea(1024*1024)
      , sig_tab(SignatureHash(ea), SignatureEqual(ea))
      , dist_idx(0)
{
    // For the uninterpreted predicates and propositional structures inside
    // uninterpreted functions, define function not, the terms true and false,
    // and an asserted disequality true != false

    PTRef t = logic.getTerm_true();
    PTRef f = logic.getTerm_false();
    constructTerm(t);
    constructTerm(f);
    ERef_True = termToERef[t];
    ERef_False = termToERef[f];
}

ERef EnodeStore::addAnonTerm(PTRef term) {
    if (termToERef.has(term))
        return termToERef[term];

    SymRef symref = logic.getSym_anon();
    ERef newEnode = ea.alloc(symref, ERefSpan(nullptr, 0) , term);
    termToERef.insert(term, newEnode);
    assert(not ERefToTerm.has(newEnode));
    ERefToTerm.insert(newEnode, term);
    termEnodes.push(newEnode);
    return newEnode;
}

//
// Add a term to enode store
//
ERef EnodeStore::addTerm(PTRef term) {
    if (termToERef.has(term))
        return termToERef[term];

    Pterm const & pterm = logic.getPterm(term);
    SymRef symref = pterm.symb();
    vec<ERef> args;
    args.capacity(pterm.nargs());
    for (PTRef arg : pterm) {
        assert(termToERef.has(arg));
        args.push(termToERef[arg]);
    }
    ERef newEnode = ea.alloc(symref, ERefSpan(args.begin(), args.size_()) , term);
    // Term's signature must not exist.  Otherwise the term would have two different signatures.
    assert(not containsSig(newEnode));
    insertSig(newEnode);
    termToERef.insert(term, newEnode);
    assert(not ERefToTerm.has(newEnode));
    ERefToTerm.insert(newEnode, term);
    termEnodes.push(newEnode);
    return newEnode;
}

/**
 * Determine if a given term represented by the PTRef tr requires an enode term.
 * @param tr the PTRef
 * @return true tr needs an enode, false otherwise.
 * @note Could be implemented in Logic as well.
 */
bool EnodeStore::needsEnode(PTRef tr) const {
    if (logic.isTrue(tr) || logic.isFalse(tr)) {
        return true;
    } else if (logic.isUFTerm(tr)) {
        return true;
    } else if (logic.isUFEquality(tr)) {
        return true;
    } else if (logic.appearsInUF(tr)) {
        return true;
    } else if (logic.isUP(tr)) {
        return true;
    } else if (logic.isDisequality(tr)) {
        return true;
    } else {
        return false;
    }
}

/**
 * Construct an Enode for a given PTRef, assuming that all the child PTRefs have
 * already been introduced an Enode.  In case of a Boolean return valued Enode,
 * add also an enode of the negation of the PTRef.  If the Boolean Enode is
 * non-atomic, no child Enodes will be constructed.
 * @param tr The PTRef for which the Enode(s) will be constructed
 * @return a vector of <PTRef,ERef> pairs consisting either of a single element
 * if the PTRef is non-boolean; two elements, the first of which corresponds to
 * the positive form and and the second the negated form of the PTRef tr; or is empty
 * if the PTRef has already been inserted.
 */
vec<PTRefERefPair> EnodeStore::constructTerm(PTRef tr) {

    assert(needsEnode(tr));

    if (termToERef.has(tr))
        return {};

    vec<PTRefERefPair> new_enodes;

    if (logic.isDisequality(tr)) {
        addDistClass(tr);
    }

    bool makeRecursiveDefinition = needsRecursiveDefinition(tr);
    ERef er = makeRecursiveDefinition ? addTerm(tr) : addAnonTerm(tr);
    new_enodes.push({tr, er});

    if (logic.hasSortBool(tr)) {
        // Add the negated term
        assert(logic.isBooleanOperator(tr) || logic.isBoolAtom(tr) || logic.isTrue(tr) || logic.isFalse(tr) || logic.isEquality(tr) || logic.isUP(tr) || logic.isDisequality(tr));
        assert(not logic.isNot(tr));
        PTRef tr_neg = logic.mkNot(tr);
        ERef er_neg = addTerm(tr_neg);
        new_enodes.push({tr_neg, er_neg});
    }

    return new_enodes;
}

bool EnodeStore::needsRecursiveDefinition(PTRef tr) const {
    bool recdef = true;
    for (auto ch : logic.getPterm(tr)) {
        recdef &= needsEnode(ch);
    }
    return recdef;
}
