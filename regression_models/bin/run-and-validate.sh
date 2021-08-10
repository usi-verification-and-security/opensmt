#!/bin/bash

function get_abs_path {
  echo $(cd $(dirname $1); pwd)/$(basename $1)
}

SCRIPT_ROOT=$(get_abs_path $(dirname $0))
DEFAULTOSMT=${DEFAULTOSMT:-~/bin/opensmt}
DEFAULTSCRAMBLER=${SCRAMBLER:-~/bin/scrambler}
DEFAULTCHECKER=${CHECKER:-~/bin/ModelValidator}
DEFAULTOUTDIR=./out/
DEFAULTPRESERVE=false

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

usage="Usage: $0 [-h] [-o <osmt2-binary>] [-s <scrambler>] [-c <checker>] [ -d <output-directory> ] [-p <true|false>] <file>"

while [ $# -gt 0 ]; do
    case $1 in
      -h|--help)
        echo "${usage}"
        exit 1
        ;;
      -o|--osmt-binary)
        binary=$2
        ;;
      -s|--scrambler)
        scrambler=$2
        ;;
      -c|--checker)
        checker=$2
        ;;
      -d|--out-dir)
        outdir=$2
        ;;
      -p|--preserve-tmp-output)
        preserve=$2
        ;;
      -*)
        echo "Error: invalid option '$1'"
        exit 1
        ;;
      *)
        break
    esac
    shift; shift
done

if [ $# == 0 ]; then
    echo $usage;
    exit 1
fi

if [ -z ${binary} ]; then
    binary=${DEFAULTOSMT}
fi

if [ -z ${scrambler} ]; then
    scrambler=${DEFAULTSCRAMBLER}
fi

if [ -z ${checker} ]; then
    checker=${DEFAULTCHECKER}
fi

if [ -z ${outdir} ]; then
    outdir=${DEFAULTOUTDIR}
fi

if [ -z ${preserve} ]; then
    preserve=${DEFAULTPRESERVE}
fi

[ -x ${scrambler} ] || \
    (echo "Scrambler not found or not executable: ${scrambler}"; exit 1)

[ -x ${checker} ] || \
    (echo "Checker not found or not executable: ${checker}"; exit 1)

tmpin=${TMPDIR}/file.smt2
tmpout=${TMPDIR}/file.out

mkdir -p ${outdir}

${scrambler} -seed "0" -gen-model-val true < $1 > ${tmpin}

sh -c "\
    ulimit -St 10;
    ulimit -Sv 4000000
    ${binary} ${tmpin}" \
        > ${tmpout} 2>/dev/null

output=${outdir}/$(basename $1 .smt2).out
if [[ $(grep '^sat' ${tmpout}) ]]; then
    sh -c "\
        ulimit -St 10;
        ulimit -Sv 4000000;
        ${checker} --smt2 ${tmpin} --model ${tmpout}" \
            > ${output}
    grep "model_validator_status=VALID" ${output} >/dev/null || \
        (echo "Invalid model for $1"; exit 1)
else
    echo "not sat"
    exit 1
fi

if [[ ${preserve} == "true" ]]; then
    echo "Left the annotated instance and the model to ${tmpin} and ${tmpout}"
    echo "Left the model validation output to ${output}"
else
    rm -rf ${tmpin} ${tmpout} ${output} ${outdir}
fi

