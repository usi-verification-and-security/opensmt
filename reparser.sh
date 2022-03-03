#bash!
symbols='abcdefghijklmnopqrstuvwxyzABCDEFGHIGKLMNOPQRSTUVYXWZ'  # Stupid SO: '
count_symbols=${#symbols}
(( length = RANDOM % 6 + 10 ))
assert_name=""
asserts=0
for i in $(seq 1 $length) ; do
    assert_name+=${symbols:RANDOM % count_symbols:1}
done


i=1;
j=0;
assert_regex="\(assert .*\)"
info_regex="\(set-info \:status sat\)"
exit="\(exit\)"
for FILE in *.smt2;
do
    ok=0
    new_file='(set-option :produce-interpolants true)\n';
    interpolants_t='(get-interpolants (and ) (and ))'
    echo $FILE
#    echo $interpolants_t
    asserts=0
    i=1
    while IFS= read -r line
    do
      if [[ "$line" =~ $assert_regex ]]
      then
        asserts=1
#        echo $i;
#        echo $line;
        assert_name=""
        (( length = RANDOM % 6 + 10 ))
        for j in $(seq 1 $length) ; do
            assert_name+=${symbols:RANDOM % count_symbols:1}
        done
        new_file="$new_file$(echo $line | sed "s/(assert \(.*\))/(assert (! \1 :named $assert_name ))/g")\n"
#        sed -e "$i s/(assert \(.*\))/(assert (! \1 :named $assert_name ))/g" $FILE > temp.txt;
        if [ $((i%2)) == 1 ]
        then
          interpolants_t=$(echo $interpolants_t | sed -e "/(get-interpolants/ s/(get-interpolants (\(.*\)) (\(.*\)))/(get-interpolants (\1$assert_name ) (\2))/g")
        else
          interpolants_t=$(echo $interpolants_t | sed -e "/(get-interpolants/ s/(get-interpolants (\(.*\)) (\(.*\)))/(get-interpolants (\1) (\2$assert_name ))/g")
        fi
#        echo $interpolants_t
#        cat temp.txt > $FILE;
        let i++;
      else
          if [[ "$line" =~ $info_regex ]]
          then
            ok=1
            rm $FILE
            echo "removed $FILE"
            break
          fi
          if [[ "$line" =~ $exit ]]
          then
            break
          fi
          new_file="$new_file$line"
       fi
#      echo $line;
      if [ $asserts == 0 ]
      then
        let i++;
      fi
    done < $FILE
    if [ $ok == 0 ]
    then
      new_file="$new_file$interpolants_t";
      cat new_file > $FILE;
    fi
done
