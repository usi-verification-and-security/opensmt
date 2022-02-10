#include <opensmt/opensmt2.h>
#include <stdio.h>

Opensmt*
pre()
{
    auto config = std::make_unique<SMTConfig>();
    const char* msg;
    config->setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    Opensmt* osmt = new Opensmt(opensmt_logic::qf_lra, "test solver", std::move(config));
    return osmt;
}

int main()
{
    
    Opensmt* osmt = pre();
    SMTConfig& c = osmt->getConfig();
    MainSolver& mainSolver = osmt->getMainSolver();
    auto & logic = osmt->getLRALogic();

    // Let's build two assertions
 
    // Create vars
    PTRef x1 = logic.mkRealVar("x1");
    PTRef x2 = logic.mkRealVar("x2");
    PTRef x3 = logic.mkRealVar("x3");
    PTRef x4 = logic.mkRealVar("x4");

    // First assertion (and (<= x1 x2) (<= x3 x4))
    PTRef le1 = logic.mkLeq(x1, x2);
    PTRef le2 = logic.mkLeq(x3, x4);
    vec<PTRef> args1;
    args1.push(le1);
    args1.push(le2);
    PTRef ass1 = logic.mkAnd(args1);

    // Second assertion (and (<= x2 x3) (< x4 x1))
    PTRef le3 = logic.mkLeq(x2, x3);

    PTRef l4 = logic.mkLt(x4, x1);
    vec<PTRef> args2;
    args2.push(le3);
    args2.push(l4);
    PTRef ass2 = logic.mkAnd(args2);

    char* msg_2;
    mainSolver.insertFormula(ass1, &msg_2);
    mainSolver.insertFormula(ass2, &msg_2);

    // Check
    sstat r = mainSolver.check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
    {
        printf("unsat\n");
        // Set labeling function
        const char* msg;
        c.setOption(SMTConfig::o_itp_bool_alg, SMTOption(0), msg);
        // Create the proof graph
        auto itp_context = mainSolver.getInterpolationContext();

        // Create the partitioning mask
        // Mask has first partition in A and second in B
    	// This is the way that OpenSMT represents partitions \.
        //ipartitions_t mask = 1;
        //mask <<= 1;
	    // HighFrog has another representation, which in this case would be
    	vector<unsigned> part;
	    part.push_back(0);
    	// It can be converted to OpenSMT's representation via
	    ipartitions_t mask = 0;
    	for(unsigned i = 0; i < part.size(); ++i)
	    	setbit(mask, part[i] + 1);

        vector<PTRef> itps;
        itp_context->getSingleInterpolant(itps, mask);
        cerr << ";Interpolant:\n;" << logic.printTerm(itps[0]) << endl;
    }
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
