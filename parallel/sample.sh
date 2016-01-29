#!/bin/bash

PYTHON='python' # this should be the command to python 2.7
OPENSMT=../opensmt
OPENSMT_SOLVER=./clause_sharing/build/solver_opensmt
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

function require_clauses {
    require ${HEURISTIC}

    if ! (check redis-server || check ./clause_sharing/src/deps/redis-server); then
        cd clause_sharing/src/deps
        if [ ! -d "redis-stable" ]; then
            info -n 'Downloading REDIS... '
            require wget
            require tar
            wget http://download.redis.io/redis-stable.tar.gz
            tar xzf redis-stable.tar.gz
            rm redis-stable.tar.gz
            sussess 'done'
            cd redis-stable
            info 'Compiling REDIS... '
            make
            success 'done'
            cd -
        fi
        require ./redis-stable/src/redis-server
        require ./redis-stable/src/redis-cli
        ln -s ./redis-stable/src/redis-cli ./redis-stable/src/redis-server .
        cd ../../..
    fi

    if (exec 9<>/dev/tcp/127.0.0.1/6379) &>/dev/null; then
        echo
        info -n 'TCP port 6379 is open for listening. '
        echo 'Assuming REDIS-SERVER already running'
        echo
    else
        info -n 'Starting REDIS-SERVER... '
        if check redis-server; then
            redis-server &>/dev/null &
        else
            ./clause_sharing/src/deps/redis-server &>/dev/null &
        fi
        success 'done'
    fi
    exec 9>&-
    exec 9<&-

}

clauses=false
mode='_scattering'
timeout=1000
splits=2
solvers=1
cport=5000
wport=3000

show_help() {
	echo "Usage $0 [-r][-t TIMEOUT=$timeout][-s SPLIT_NUMBER=$splits][-n SOLVERS=$solvers] FILE1.smt2 [FILE2.smt [...]]"
	echo
	echo "-r    : use clause sharing (default $clauses)"
	#echo "-S    : use scattering (default $mode)"
	exit 0
}

while getopts "hrt:s:n:p:" opt; do
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
    require_clauses
fi

info '! PLEASE READ THE README FIRST !'
echo
echo "number of splits:             $splits"
echo "split mode:                   $mode"
echo "timeout:                      $timeout"
echo "solvers:                      $solvers"
echo

SERVER_OUT=server${solvers}-s${splits}-${clauses}.out
echo -n 'starting server... '
${PYTHON} ${SERVER} -c 5000 -w 3000 -t ${timeout} -d -f ${SERVER_DIR}/${mode} -s ${splits} -o ${OPENSMT} > ${SERVER_OUT} 2>/dev/null &
server_pid=$!
sleep 1
success 'done'

echo 'sending the files to the server... '
${PYTHON} ${SERVER_COMMAND} 127.0.0.1 -p 5000 $@
success 'done'

echo

if ${clauses}; then
    echo -n 'starting heuristic... '
    ./run-heuristic.sh ${HEURISTIC} -r127.0.0.1:6379 > heuristic.out 2>/dev/null &
    heuristic_pid=$!
    #nohup ${HEURISTIC} -r 127.0.0.1:$((6380 + ${port_offset})) > heuristic_${port_offset}.out &
    success 'done'
    echo
fi

OPENSMT_OUT=solvers${solvers}-s${splits}-${clauses}_${port_offset}.out
> ${OPENSMT_OUT}
echo -n 'starting solvers '
for i in $(seq ${solvers})
do
    if ${clauses}; then
        ${OPENSMT_SOLVER} -s127.0.0.1:3000 -r127.0.0.1:6379 >> ${OPENSMT_OUT} 2>&1 &
    else
        ${OPENSMT_SOLVER} -s127.0.0.1:3000 >> ${OPENSMT_OUT} 2>&1 &
    fi
	echo -n "|"
done
success ' done'
echo -n 'waiting for all the problems to be solved... '
wait ${server_pid}
if ${clauses}; then
    kill -9 ${heuristic_pid}
    wait ${heuristic_pid} 2>/dev/null
    killall -9 ${HEURISTIC}
fi
success 'done!'
info "The results are in $SERVER_OUT"
success 'bye'
