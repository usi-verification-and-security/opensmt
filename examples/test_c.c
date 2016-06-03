#include <stdlib.h>
#include <stdio.h>
#include <opensmt/opensmt_c.h>

int
main(int argc, char** argv)
{
    osmt_context ctx = osmt_mk_context(qf_uf);

    osmt_expr* args = (osmt_expr*)malloc(2*sizeof(osmt_expr));
    args[0] = osmt_mk_bool_var(ctx, "a");
    args[1] = osmt_mk_not(ctx, args[0]);

    osmt_expr a = osmt_mk_and(ctx, args, 2);
    osmt_push(ctx, a);
    osmt_result r = osmt_check(ctx);

    if (r == l_true)
        printf("sat\n");
    else if (r == l_false)
        printf("unsat\n");
    else if (r == l_undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
