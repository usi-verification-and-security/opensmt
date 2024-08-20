if [[ -z $1 ]]; then
   CMD=(build-debug/opensmt)
else
   CMD=("$@")
fi

for f in regression/QF_LRA/*.smt2; do out=$("${CMD[@]}" $f) || { echo $f; exit 1; }; diff -q <(echo "$out") ${f}.expected.out && continue; diff <(<<<"$out") ${f}.expected.out; exit 1; done

echo "Success."
