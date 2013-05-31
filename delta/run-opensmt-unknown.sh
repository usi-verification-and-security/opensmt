#!/usr/bin/zsh

# 0 - sat
# 1 - unsat
# 2 - unknown

osmt=/u1/home/aehyvari/src/OpenSMT/opensmt-dev/TRUNK/opensmt
z3=/u1/home/aehyvari/src/z3/z3/bin/external/z3

out_osmt=`$osmt $1`
rval=$?
echo $out_osmt
res_osmt=2

if [[ $out_osmt == 'sat' ]]; then
    return 0
elif [[ $out_osmt == 'unsat' ]]; then
    return 0
fi
if [[ $rval -eq 0 ]]; then
    return 0
fi
return 1

