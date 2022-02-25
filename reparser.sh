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
for FILE in *.smt2;
do
    sed -e '1 s/\(.*\)/(set-option :produce-interpolants true)\n\1/g' $FILE > temp.txt;
    cat temp.txt > $FILE;
    sed -e '/(check-sat)/ s/\(.*\)/\1\n(get-interpolants (and ) (and ))\n/g' $FILE > temp.txt;
    cat temp.txt > $FILE;
    echo $FILE
    asserts=0
    i=1
    while IFS= read -r line
    do
      if [[ "$line" =~ $assert_regex ]]
      then
        asserts=1
        echo $i;
#        echo $line;
        assert_name=""
        (( length = RANDOM % 6 + 10 ))
        for j in $(seq 1 $length) ; do
            assert_name+=${symbols:RANDOM % count_symbols:1}
        done
        sed -e "$i s/(assert \(.*\))/(assert (! \1 :named $assert_name ))/g" $FILE > temp.txt;
        cat temp.txt > $FILE;
        if [ $((i%2)) == 1 ]
        then
          sed -e "/(get-interpolants/ s/(get-interpolants (\(.*\)) (\(.*\)))/(get-interpolants (\1$assert_name ) (\2))/g" $FILE > temp.txt;
        else
          sed -e "/(get-interpolants/ s/(get-interpolants (\(.*\)) (\(.*\)))/(get-interpolants (\1) (\2$assert_name ))/g" $FILE > temp.txt;
        fi
        cat temp.txt > $FILE;
        let i++;
      fi
#      echo $line;
      if [ $asserts == 0 ]
      then
        let i++;
      fi
    done < $FILE
done
