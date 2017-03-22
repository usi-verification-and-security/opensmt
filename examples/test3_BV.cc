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
    CUFTheory cuftheory(c);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);
    CUFLogic& logic = cuftheory.getLogic();

    BVLogic bvlogic(c);

    //PTRef eq = logic.mkEq(yz,zy);   //for all
    //PTRef eq_neg = logic.mkNot(eq); // the negation of formula

    PTRef y_bb = bvlogic.mkNumVar("y");
    PTRef z_bb = bvlogic.mkNumVar("z");
    PTRef yz_bb = bvlogic.mkBVBwAnd(y_bb, z_bb);

    PTRef z2_bb = bvlogic.mkNumVar("z");
    PTRef y2_bb = bvlogic.mkNumVar("y");
    PTRef zy_bb = bvlogic.mkBVBwAnd(z2_bb, y2_bb);

    PTRef eq_bb = bvlogic.mkEq(yz_bb, zy_bb);
    PTRef eq_bb_neg = bvlogic.mkBVNot(eq_bb);

    mainSolver.push(eq_bb_neg);
    sstat r = mainSolver.check();

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
