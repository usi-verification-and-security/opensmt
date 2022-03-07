#!/bin/bash

usage="Usage: $0 [-h] -i <base> -s <split> -o <output>"

while [ $# -gt 0 ]; do
    case $1 in
        -h|--help)
            echo "$usage"
            exit 1
            ;;
        -i|--input)
            base=$2
            ;;
        -s|--split)
            split=$2
            ;;
        -o|--output)
            output=$2
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

if [ -z $base ] || [ ! -f $base ]; then
    echo "Basefile not provided or not accessible: $base"
    echo $usage
    exit 1
fi

if [ -z $split ] || [ ! -f $split ]; then
    echo "Split file not provided or not accessible: $split"
    echo $usage
    exit $1
fi

if [ -z $output ]; then
    echo "Outputfile not provided"
    output=/dev/stdout
    echo "Using $output"
fi

bunzip2 -c $base |grep -v '^(check-sat)\|(exit)\|(set-info :status \(sat\|unsat\))$' > $output
cat $split >> $output
cat << __EOF__ >> $output
(check-sat)
(exit)
__EOF__


