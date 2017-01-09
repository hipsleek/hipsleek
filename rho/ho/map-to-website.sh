#create a list of source files in website
WEB=/home/project/public_html/conchip/src/hip/


cp ../../prelude.ss $WEB/../../cgi-bin/
cp ../../hip $WEB/../../cgi-bin/conchip

#===================
cp multi-join1.ss $WEB/1.ss
cp multi-join2.ss $WEB/2.ss
cp mapreduce.ss $WEB/3.ss
cp latch-exp1.ss $WEB/4.ss
cp latch-exp2.ss $WEB/5.ss
cp lock-exp2.ss $WEB/6.ss
# cp lock-exp4.ss $WEB/7.ss #need to eliminate the comments
cp fibonacci.ss $WEB/8.ss
cp parallel-mergesort.ss $WEB/9.ss
cp parallel-quicksort.ss $WEB/10.ss
cp threadpool.ss $WEB/11.ss
cp deadpool.ss $WEB/12.ss


# #===================
# # Spare for future use

# cp $WEB/11.ss
# cp $WEB/12.ss
# cp $WEB/13.ss
# cp $WEB/14.ss
# cp $WEB/15.ss
# cp $WEB/16.ss
# cp $WEB/17.ss
# cp $WEB/18.ss
# cp $WEB/19.ss
# cp $WEB/20.ss
# cp $WEB/21.ss
# cp $WEB/22.ss
# cp $WEB/23.ss

