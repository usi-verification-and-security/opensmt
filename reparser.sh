#bash!
for FILE in $1;
do
    echo -e "$FILE\nLoops Rule\!" > $FILE;
    while IFS= read -r line
    do
      echo "$line"
    done << $FILE

done
