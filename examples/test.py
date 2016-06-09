#/usr/bin/env python
from opensmt import *

if __name__ == '__main__':
    ctx = mkContext(qf_lra)

    f1 = mkOr(ctx, [mkAnd(ctx, [mkBool(ctx, "a"), mkBool(ctx, "b")]), mkNot(ctx, mkBool(ctx, "c"))])

    f2 = mkImpl(ctx, f1, mkLeq(ctx, mkNum(ctx, 1), mkReal(ctx, "r")))
    printTerm(ctx, f2)
    print ""

    push(ctx, f2)
    r = osmt_check(ctx)

    if (r == l_false):
        print "false"
    elif (r == l_true):
        print "true"
    elif (r == l_undef):
        print "undef"
    else:
        print "solver returned something strange: %d" % r

