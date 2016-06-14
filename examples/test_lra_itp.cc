#include <opensmt/opensmt2.h>
#include <stdio.h>

Opensmt*
pre()
{
    Opensmt* osmt = new Opensmt(opensmt_logic::qf_lra);
    return osmt;
}

int
main(int argc, char** argv)
{
    
    Opensmt* osmt = pre();
    SMTConfig& c = osmt->getConfig();
    MainSolver& mainSolver = osmt->getMainSolver();
    SimpSMTSolver& solver = osmt->getSolver();
    LRALogic& logic = osmt->getLRALogic();

    /*
    SMTConfig c;
    UFTheory uftheory(c);
    THandler thandler(c, uftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);
    Logic& logic = thandler.getLogic();
    */

    const char* msg;
    c.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    
    // Let's build two assertions
 
    // Create vars
    PTRef x1 = logic.mkRealVar("x1");
    PTRef x2 = logic.mkRealVar("x2");
    PTRef x3 = logic.mkRealVar("x3");
    PTRef x4 = logic.mkRealVar("x4");

    // First assertion (and (<= x1 x2) (<= x3 x4))
    vec<PTRef> leq_args;
    leq_args.push(x1);
    leq_args.push(x2);
    PTRef le1 = logic.mkRealLeq(leq_args);
    leq_args.clear();
    leq_args.push(x3);
    leq_args.push(x4);
    PTRef le2 = logic.mkRealLeq(leq_args);
    vec<PTRef> args1;
    args1.push(le1);
    args1.push(le2);
    PTRef ass1 = logic.mkAnd(args1);

    // Second assertion (and (<= x2 x3) (< x4 x1))
    leq_args.clear();
    leq_args.push(x2);
    leq_args.push(x3);
    PTRef le3 = logic.mkRealLeq(leq_args);
    leq_args.clear();
    leq_args.push(x4);
    leq_args.push(x1);
    PTRef l4 = logic.mkRealLt(leq_args);
    vec<PTRef> args2;
    args2.push(le3);
    args2.push(l4);
    PTRef ass2 = logic.mkAnd(args2);

    mainSolver.push(ass1);
    mainSolver.push(ass2);

    // Check
    sstat r = mainSolver.check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
    {
        printf("unsat\n");

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
    }
    else if (r == s_Undef)
        printf("unknowon\n");
    else
        printf("error\n");

    return 0;
}
