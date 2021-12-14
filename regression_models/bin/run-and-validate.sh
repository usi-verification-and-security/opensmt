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

output=${outdir}/$(basename $1 .smt2).out
tmpin=${TMPDIR}file.smt2
tmpout=${TMPDIR}file.out

TMPDIR=$(mktemp -d)
trap "[ ${preserve} == "true" ] && (\
    printf 'Left the annotated instance the model, and validation output to \n - %s\n - %s\n - %s\n' ${tmpin} ${tmpout} ${output}) \
        || rm -rf ${output} ${tmpin} ${tmpout} ${TMPDIR}" EXIT

mkdir -p ${outdir}

${scrambler} -seed "0" -gen-model-val true < $1 2>&1 > ${tmpin} \
    | grep "ERROR: " >/dev/null && \
      echo "Error parsing input file $1" && \
      exit 1

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
    if (! $(grep "model_validator_status=VALID" ${output} >/dev/null)); then
        echo "Invalid model: $1";
        exit 1
    fi
else
    echo "Not satisfiable: $1"
    exit 1
fi

if [[ ${preserve} == "true" ]]; then
    echo "Left the annotated instance and the model to ${tmpin} and ${tmpout}"
    echo "Left the model validation output to ${output}"
fi

