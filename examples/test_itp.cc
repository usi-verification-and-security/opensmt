#include <opensmt/opensmt2.h>
#include <stdio.h>

Opensmt*
pre()
{
    auto config = std::make_unique<SMTConfig>();
    config->setOption(SMTConfig::o_produce_inter, SMTOption(true));
    Opensmt* osmt = new Opensmt(opensmt_logic::qf_lra, "test solver", std::move(config));
    return osmt;
}

int main()
{
    
    Opensmt* osmt = pre();
    SMTConfig& c = osmt->getConfig();
    MainSolver& mainSolver = osmt->getMainSolver();
    Logic& logic = osmt->getLogic();
    
    // Let's build two assertions

    // First assertion (a /\ b)
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    vec<PTRef> args1;
    args1.push(a);
    args1.push(b);
    PTRef ass1 = logic.mkAnd(args1);

    // Second assertion (!a \/ !b)
    PTRef neg_a = logic.mkNot(a);
    PTRef neg_b = logic.mkNot(b);
    vec<PTRef> args2;
    args2.push(neg_a);
    args2.push(neg_b);
    PTRef ass2 = logic.mkOr(args2);

    char* msg2;
    mainSolver.insertFormula(ass1, &msg2);
    mainSolver.insertFormula(ass2, &msg2);

    // Check
    sstat r = mainSolver.check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
    {
        printf("unsat\n");
        // Set labeling function
        c.setOption(SMTConfig::o_itp_bool_alg, SMTOption(0));

        auto itp_context = mainSolver.getInterpolationContext();
        // Create the partitioning mask
        // Mask has first partition in A and second in B
    	// This is the way that OpenSMT represents partitions \.
        //ipartitions_t mask = 1;
        //mask <<= 1;
	    // HighFrog has another representation, which in this case would be
    	std::vector<unsigned> part;
	    part.push_back(0);
    	// It can be converted to OpenSMT's representation via
	    ipartitions_t mask = 0;
    	for(unsigned i = 0; i < part.size(); ++i)
	    	opensmt::setbit(mask, part[i] + 1);

        std::vector<PTRef> itps;
        itp_context->getSingleInterpolant(itps, mask);
        std::cerr << ";Interpolant:\n;" << logic.printTerm(itps[0]) << std::endl;
    }
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
