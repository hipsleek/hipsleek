for FN in `ls ref`
do
   #wc tests/$FN
   echo "hg mv $FN ${FN}.out"
done
