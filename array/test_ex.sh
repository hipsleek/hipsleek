#echo $2
timeout 10s $1 $2 --print-min --ato $3 > result/$2.out
#timeout 10s $1 $2.ss  $3 > result/$2.ss.out
#echo $?
OUT=$?
fn=$2
if [ $OUT -eq 124 ];then
   echo "10s Timeout for ${fn}"
else
   echo "Executed ${fn}"
fi