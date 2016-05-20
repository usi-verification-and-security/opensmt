res=`z3 -v:1 -smt2 $1`
ret_val=0;
if [ "$res" = "unsat" ]
then 
ret_val=0
else 
if [ "$res" = "sat" ] 
then 
ret_val=1
else 
echo "$res"
ret_val=2
fi
fi
#echo Result: $res Return value: $ret_val
exit $ret_val
