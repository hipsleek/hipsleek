timeout 10s $1 examples/$2.ss > result/out.$2
#echo $?
OUT=$?
fn=$2.ss
if [ $OUT -eq 124 ];then
   echo "10s Timeout for ${fn}"
fi