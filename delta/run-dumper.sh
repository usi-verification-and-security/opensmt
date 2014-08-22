#!/usr/bin/env bash

osmt2=/home/hyvaeria/src/OpenSMT/opensmt_antti/opensmt-dev/trunk/opensmt

if [[ $# != 1 ]]; then
    echo "Usage $0 <file>"
    exit 1
fi

opts_file=$(dirname $1)/$(basename $1 .smt2)_tmp.smt2
osmt2_file=$(dirname $1)/$(basename $1 .smt2)_tmp.osmt2

cat > ${opts_file} << __EOF__
(set-option :dump-state "${osmt2_file}")
(set-option :dump-only true)
__EOF__

grep '(check-sat)' $1 > /dev/null || exit 2
out_dump=`$osmt2 $opts_file $1`
rm ${opts_file}

if [[ $out_dump == 'unknown' ]]; then
    cat > ${opts_file}  << __EOF__
(set-logic QF_UF)
(read-state "${osmt2_file}")
(check-sat)
(exit)
__EOF__

    $osmt2 ${opts_file}
elif [[ $out_dump == 'sat' ]]; then
    echo sat
elif [[ $out_dump == 'unsat' ]]; then
    echo unsat
fi

rm ${osmt2_file} ${opts_file}
