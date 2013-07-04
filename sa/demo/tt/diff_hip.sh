function EX 
{
diff tests/$1.out2 tests/$1.ref2 -b  > _XYZ
if [ -s _XYZ ]
then
echo =======
echo " $1  "
echo =======
cat _XYZ
fi
}
EX set-tail-2.ss 
EX sll-dll.ss 
EX last-2.ss  
EX dll-append_paper.ss 
EX zip_paper_leq.ss 
EX tll.ss 

