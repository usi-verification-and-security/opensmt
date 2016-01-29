#!/bin/bash

SERVER_OUT='./server.out'
PYTHON='python' # this should be the command to python 2.7
OPENSMT=../opensmt
OPENSMT_SOLVER=/home/matteo/bin/solver_opensmt
SERVER_DIR=./server
SERVER=${SERVER_DIR}/sserver.py
SERVER_COMMAND=${SERVER_DIR}/command.py
HEURISTIC=./clause_sharing/build/heuristic
REDIS_SERVER=./clause_sharing/src/deps/redis-server
REDIS_CLIENT=./clause_sharing/src/deps/redis-cli

# ----------------

trap '' HUP

function info {
  tput bold
  echo "$@"
  tput sgr0
}

function success {
	tput setaf 2
	info "$@"
}

function error {
	tput setaf 9
	info "$@"
}

function check {
    command -v $1 >/dev/null 2>&1
    return $?
}

function require {
    check $1 || { error "Missing program '$1'."; info $2; echo 'Aborting.' >&2; exit 1;}
}

clauses=false
mode='_lookahead'
timeout=1000
splits=2
solvers=1
port_offset=0
cport=5000
wport=3000

show_help() {
	echo "Usage $0 [-r][-S][-t TIMEOUT=$timeout][-s SPLIT_NUMBER=$splits][-n SOLVERS=$solvers][-p PORT_OFFSET=$port_offset] FILE1.smt2 [FILE2.smt [...]]"
	echo
	echo "-r    : use clause sharing (default $clauses)"
	echo "-S    : use scattering (default $mode)"
	exit 0
}

while getopts "hrSt:s:n:p:" opt; do
	case "$opt" in
		h|\?)
            show_help
        	;;
        r)  clauses=true
            ;;
		S)  mode='_scattering'
		    ;;
		t)	timeout=$OPTARG
       		;;
		s)	splits=$OPTARG
		    ;;
		n)	solvers=$OPTARG
       		;;
       	p)	port_offset=$OPTARG
       		;;
	esac
done

shift $((OPTIND-1))

if [ $# -le 0 ]; then
    error '.smt2 file(s) missing!'
    show_help
    exit
fi

require ${PYTHON}
require ${OPENSMT} 'Please compile OpenSMT2'
require ${OPENSMT_SOLVER}
require ${SERVER}
require ${SERVER_COMMAND}

if ${clauses}; then
    require ${HEURISTIC}
fi

if [ $((${solvers}%8)) -ne 0 -a ${solvers} -ge 8 -o ${solvers} -le 0 ]; then
    error "SOLVERS must be 1 to 8 or multiples of 8"
    exit
fi


info '! PLEASE READ THE README FIRST !'
echo
echo "number of splits:             $splits"
echo "split mode:                   $mode"
echo "timeout:                      $timeout"
echo "solvers:                      $solvers"
echo "port offset:                  $port_offset"
echo

echo -n 'starting server... '
nohup ${PYTHON} ${SERVER} -c $((5000 + ${port_offset})) -w $((3000 + ${port_offset})) -t ${timeout} -d -f ${SERVER_DIR}/${mode} -s ${splits} -o ${OPENSMT} > server${solvers}-s${splits}-${clauses}_${port_offset}.out 2>/dev/null &
sleep 1
success 'done'

echo 'sending the files to the server... '
${PYTHON} ${SERVER_COMMAND} 127.0.0.1 -p $((5000 + ${port_offset})) $@
success 'done'

if ${clauses}; then
    echo -n 'starting REDIS... '
    ${REDIS_SERVER} --port $((6380 + ${port_offset})) > /dev/null &
    sleep 1
    echo 'config set save ""' | ${REDIS_CLIENT} -p $((6380 + ${port_offset}))
    echo 'config get save' | ${REDIS_CLIENT} -p $((6380 + ${port_offset}))
    sleep 1
    success 'done'
    echo -n 'starting heuristic... '
    nohup ./run-heuristic.sh ${HEURISTIC} -r127.0.0.1:$((6380 + ${port_offset})) > heuristic_${port_offset}.out &
    #nohup ${HEURISTIC} -r 127.0.0.1:$((6380 + ${port_offset})) > heuristic_${port_offset}.out &
    success 'done'
    solver_redis_arg="-r10.1.1.1:$((6380 + ${port_offset}))"
else
    solver_redis_arg="-R"
fi

if [ ${solvers} -le 7 ]; then
    printf "#!/bin/bash
#SBATCH --time 10:00:00
#SBATCH -N 1
#SBATCH -pbatch

mpiexec -np ${solvers} ${OPENSMT_SOLVER} ${solver_redis_arg} -s10.1.1.1:$((3000 + ${port_offset}))
" | sbatch --output=solvers${solvers}-s${splits}-${clauses}_${port_offset}.out
else
    printf "#!/bin/bash
#SBATCH --time 10:00:00
#SBATCH -N $((${solvers}/8))
#SBATCH -pbatch

mpiexec ${OPENSMT_SOLVER} ${solver_redis_arg} -s10.1.1.1:$((3000 + ${port_offset}))
" | sbatch --output=solvers${solvers}-s${splits}-${clauses}_${port_offset}.out
fi
