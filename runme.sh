ROOT_DIR=$(dirname "$0")

files_file="$1"
files_name=$(basename "$files_file")

logic="${files_name%_files*}"

version=opensmt

DATA_DIR=$(dirname "$files_file")
RESULTS_DIR="$DATA_DIR/$version/$logic"
mkdir -p "$RESULTS_DIR" >/dev/null || exit $?

# [[ -z $TIMEOUT ]] && TIMEOUT=300
[[ -z $TIMEOUT ]] && TIMEOUT=1200


err=$(mktemp)
out=$(mktemp)
tfile=$(mktemp)

export TIMEFORMAT='%2R'

function cleanup {
  if [[ -n $1 && $1 != 0 ]]; then
    [[ -r $out ]] && mv $out ERROR_${version}_${files_name}.out
    [[ -r $err ]] && mv $err ERROR_${version}_${files_name}.err
    [[ -r $tfile ]] && mv $tfile ERROR_${version}_${files_name}.time
  else
    rm -f $err
    rm -f $out
    rm -f $tfile
  fi

  [[ -n $1 ]] && exit $1
}

trap 'cleanup 1' INT TERM QUIT

    while read file; do
      timeout $TIMEOUT bash -c "{ time \"$ROOT_DIR/build/opensmt\" \"$file\" >$out 2>$err ; } 2>$tfile"
      ret=$?
      if (( $ret == 0 )); then
        res=$(<$out)
      elif (( $ret == 124 )); then
        res=unknown
      fi
      [[ $res =~ (signal|memory) ]] && {
        res=mem
      }
        [[ ! $res =~ ^(unsat|sat|unknown|mem)$ || -s $err ]] && {
          printf "ERROR at %s:\nUnrecognized result:\n%s\n" "$file" "$res" >ERROR_${version}_${files_name}
          cleanup 1
        }
        [[ $res == unknown ]] && {
          printf "%s %s %s\n" "$file" $res $TIMEOUT
          continue
        }
      time=$(<$tfile)
      [[ $time =~ ^[0-9]+\.[0-9]+$ ]] || {
        printf "ERROR at %s:\nUnrecognized time:\n%s\n" "$file" "$time" >ERROR_${version}_${files_name}
        cleanup 1
      }
      [[ $res == mem ]] && res=unknown
      printf "%s %s %s\n" "$file" $res $time
    done <"$files_file" >"$RESULTS_DIR/${version}_${files_name}"

cleanup 0
