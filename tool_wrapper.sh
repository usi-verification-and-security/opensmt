opensmt $1 > toolwrappertmp 2>&1
res=`cat toolwrappertmp |grep '^sat\|^unsat'`
rm toolwrappertmp
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
exit $ret_val
