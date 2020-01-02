#include <opensmt/opensmt2.h>
#include <stdio.h>

Opensmt*
pre()
{
    Opensmt* osmt = new Opensmt(opensmt_logic::qf_lra, "Test solver");
    return osmt;
}
void
kill(Opensmt* osmt)
{
    delete osmt;
}
int
main(int argc, char** argv)
{

    Opensmt* osmt = pre();
    SMTConfig& c = osmt->getConfig();
    MainSolver& mainSolver = osmt->getMainSolver();
    SimpSMTSolver& solver = osmt->getSolver();
    LRALogic& logic = osmt->getLRALogic();

    const char* msg;
    c.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);

    // Let's build two assertions

    // Create vars
    PTRef x1 = logic.mkNumVar("x1");
    PTRef x2 = logic.mkNumVar("x2");
    PTRef x3 = logic.mkNumVar("x3");
    PTRef x4 = logic.mkNumVar("x4");

    // First assertion (and (<= x1 x2) (<= x3 x4))
    vec<PTRef> leq_args;
    leq_args.push(x1);
    leq_args.push(x2);
    PTRef le1 = logic.mkNumLeq(leq_args);
    leq_args.clear();
    leq_args.push(x3);
    leq_args.push(x4);
    PTRef le2 = logic.mkNumLeq(leq_args);
    vec<PTRef> args1;
    args1.push(le1);
    args1.push(le2);
    PTRef ass1 = logic.mkAnd(args1);

    // Second assertion (and (<= x2 x3) (< x4 2))
    leq_args.clear();
    leq_args.push(x2);
    leq_args.push(x3);
    PTRef le3 = logic.mkNumLeq(leq_args);
    leq_args.clear();
    leq_args.push(x4);
    leq_args.push(logic.mkConst("2"));
    PTRef l4 = logic.mkNumLt(leq_args);
    vec<PTRef> args2;
    args2.push(le3);
    args2.push(l4);
    PTRef ass2 = logic.mkAnd(args2);

    char* msg2;
    mainSolver.insertFormula(ass1, &msg2);
    mainSolver.insertFormula(ass2, &msg2);

    // Check
    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        ValPair v1 = mainSolver.getValue(x1);
        char* name = logic.printTerm(x1);
        printf("%s: %s\n", name, v1.val);
        free(name);
        ValPair v2 = mainSolver.getValue(x2);
        name = logic.printTerm(x2);
        printf("%s: %s\n", name, v2.val);
        free(name);
        ValPair v3 = mainSolver.getValue(x3);
        name = logic.printTerm(x3);
        printf("%s: %s\n", name, v3.val);
        free(name);
        ValPair v4 = mainSolver.getValue(x4);
        name = logic.printTerm(x4);
        printf("%s: %s\n", name, v4.val);
        free(name);

    }
    else if (r == s_False)
    {
        printf("unsat\n");
#ifdef PRODUCE_PROOF
        // Set labeling function
        c.setOption(SMTConfig::o_itp_bool_alg, SMTOption(0), msg);

        // Create the proof graph
        solver.createProofGraph();

        // Create the partitioning mask
        // Mask has first partition in A and second in B
    	// This is the way that OpenSMT represents partitions \.
        //ipartitions_t mask = 1;
        //mask <<= 1;
	    // HighFrog has another representation, which in this case would be
    	vector<int> part;
	    part.push_back(0);
    	// It can be converted to OpenSMT's representation via
	    ipartitions_t mask = 0;
    	for(int i = 0; i < part.size(); ++i)
	    	setbit(mask, part[i] + 1);

        vector<PTRef> itps;
        solver.getSingleInterpolant(itps, mask);
        cerr << ";Interpolant:\n;" << logic.printTerm(itps[0]) << endl;
#endif // PRODUCE_PROOF
    }
    else if (r == s_Undef)
        printf("unknowon\n");
    else
        printf("error\n");

    kill(osmt);
    return 0;
}
