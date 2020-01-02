/********************************************
 * Created on: Jan 17, 2017
 * Author: Sepideh Asadi
 * check the negation of : y && z == z && y
 ********************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BVLogic.h>


int
main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c);
    THandler* thandler = new THandler(c, *cuftheory);
    SimpSMTSolver* solver = new SimpSMTSolver(c, *thandler);
    MainSolver* mainSolver = new MainSolver(*thandler, c, solver, "test solver");
    CUFLogic& logic = cuftheory->getLogic();

    BVLogic bvlogic(c);

    PTRef y_bb = bvlogic.mkBVNumVar("y");
    PTRef z_bb = bvlogic.mkBVNumVar("z");
    PTRef yz_bb = bvlogic.mkBVBwAnd(y_bb, z_bb);

    PTRef z2_bb = bvlogic.mkBVNumVar("z");
    PTRef y2_bb = bvlogic.mkBVNumVar("y");
    PTRef zy_bb = bvlogic.mkBVBwAnd(z2_bb, y2_bb);

    PTRef eq_bb = bvlogic.mkBVEq(yz_bb, zy_bb);
    PTRef eq_bb_neg = bvlogic.mkBVNot(eq_bb);
    // MB: TODO: How to turn BVsort to boolean?

    mainSolver->push(eq_bb_neg);
    sstat r = mainSolver->check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
