#echo $2
timeout 10s $1 $2.ss --print-min $3 > result/$2.ss.out
#timeout 10s $1 $2.ss  $3 > result/$2.ss.out
#echo $?
OUT=$?
fn=$2.ss
if [ $OUT -eq 124 ];then
   echo "10s Timeout for ${fn}"
else
   echo "Executed ${fn}"
fi