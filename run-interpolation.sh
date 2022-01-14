#bash!
var new_file
for file in *.smt2;
do
    echo $file
    sed -n 's/^\(*\)/(set-option :produce-interpolants true)\n\1/p' $file;
#    echo $new_file
done