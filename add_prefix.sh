echo $1
cat one_line.txt $1 > tmp
cp tmp $1
rm tmp
 

