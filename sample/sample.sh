#!/bin/sh

SERVER_OUT='./server.out'
OPENSMT_OUT='./opensmt.out'
PYTHON='python' # this should be the command to python 2.7


workers=2
split=2
mode='_lookahead'

show_help() {
	echo "Usage $0 [-R][-S][-n WORKER_NUMBER=$workers][-s SPLIT_NUMBER=$split][-p PYTHON2.7_PATH=$python] FILE1.smt2 [FILE2.smt [...]]"
	echo
	echo "-R    : use clause sharing"
	echo "-S    : use scattering (default lookahead)"
	exit 0
}

while getopts "hRSn:s:" opt; do
	case "$opt" in
		h|\?)
            show_help
        	;;
        R)
            ;;
		S)  mode='_scattering'
		    ;;
		n)	workers=$OPTARG
       		;;
		s)	split=$OPTARG
		    ;;
	esac
done

shift $((OPTIND-1))

if [ $# -le 0 ]; then
    echo '.smt2 file(s) missing!'
    show_help
    exit
fi

echo '#'
echo '# ! PLEASE READ THE README FIRST !'
echo '#'
echo "# number of opensmt solvers: $workers"
echo "# number of splits: $split"
echo "# split mode: $mode"
echo '#'
echo "# SERVER stdout will be redirected to $SERVER_OUT"
echo "# OPENSMT solvers stdout and stderr will be redirected to $OPENSMT_OUT"
echo '#'
echo '# starting server... '
$PYTHON ../wserver/sserver.py -d -f ../wserver/$mode -s $split -o ../opensmt > $SERVER_OUT 2>/dev/null &
server_pid=$!
sleep 1
echo '# done'
echo '# sending the files to the server... '
$PYTHON ../wserver/command.py 127.0.0.1 $@ > /dev/null
echo '# done'
for i in $(seq $workers)
do
	echo "# starting opensmt solver $i... "
	../opensmt -s127.0.0.1:3000 > $OPENSMT_OUT 2>&1 &
	echo '# done'
done
echo '# waiting for all the problem to be solved... '
wait $server_pid
echo '# done'
echo "# The results are in $SERVER_OUT"
echo '# bye'
