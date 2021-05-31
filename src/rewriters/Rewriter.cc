//
// Created by Antti on 13.04.21.
//

#include "Rewriter.h"

template<> bool DefaultRewriterConfig<PTRef>::isEnabled(PTRef) { return true; }
template<> bool DefaultRewriterConfig<PtAsgn>::isEnabled(PtAsgn pta) { return pta.sgn == l_True; }
template<> PTRef & DefaultRewriterConfig<PTRef>::getAsgnTermRef(PTRef & tr) { return tr; }
template<> PTRef & DefaultRewriterConfig<PtAsgn>::getAsgnTermRef(PtAsgn & pta) { return pta.tr; }
template<> PTRef DefaultRewriterConfig<PTRef>::getAsgnTerm(PTRef tr) { return tr; }
template<> PTRef DefaultRewriterConfig<PtAsgn>::getAsgnTerm(PtAsgn pta) { return pta.tr; }