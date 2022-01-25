#include <opensmt/opensmt2.h>
#include <stdio.h>

Opensmt*
pre()
{
    auto config = std::unique_ptr<SMTConfig>(new SMTConfig());
    const char* msg;
    config->setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    Opensmt* osmt = new Opensmt(opensmt_logic::qf_lra, "test solver", std::move(config));
    return osmt;
}
void
kill(Opensmt* osmt)
{
    delete osmt;
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
    vec<PTRef> leq_args;
    leq_args.push(x1);
    leq_args.push(x2);
    PTRef le1 = logic.mkLeq(leq_args);
    leq_args.clear();
    leq_args.push(x3);
    leq_args.push(x4);
    PTRef le2 = logic.mkLeq(leq_args);
    vec<PTRef> args1;
    args1.push(le1);
    args1.push(le2);
    PTRef ass1 = logic.mkAnd(args1);

    // Second assertion (and (<= x2 x3) (< x4 2))
    leq_args.clear();
    leq_args.push(x2);
    leq_args.push(x3);
    PTRef le3 = logic.mkLeq(leq_args);
    leq_args.clear();
    leq_args.push(x4);
    leq_args.push(logic.mkConst("2"));
    PTRef l4 = logic.mkLt(leq_args);
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
        auto m = mainSolver.getModel();
        PTRef v1 = m->evaluate(x1);
        char* name = logic.pp(x1);
        char* value = logic.pp(v1);
        printf("%s: %s\n", name, value);
        free(name);
        free(value);
        PTRef v2 = m->evaluate(x2);
        name = logic.pp(x2);
        value = logic.pp(v2);
        printf("%s: %s\n", name, value);
        free(name);
        free(value);
        PTRef v3 = m->evaluate(x3);
        name = logic.pp(x3);
        value = logic.pp(v3);
        printf("%s: %s\n", name, value);
        free(name);
        free(value);
        PTRef v4 = m->evaluate(x4);
        name = logic.printTerm(x4);
        value = logic.printTerm(v4);
        printf("%s: %s\n", name, value);
        free(name);
        free(value);
    }
    else if (r == s_False)
    {
        printf("unsat\n");
        // Set labeling function
        const char* msg;
        c.setOption(SMTConfig::o_itp_bool_alg, SMTOption(0), msg);

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

    kill(osmt);
    return 0;
}
