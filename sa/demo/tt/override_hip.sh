function EX 
{
 cp tests/$1.out2 tests/$1$2.ref2
}

EX app5-bug-1.slk
EX set-tail-2.ss 
EX sll-dll.ss 
EX last-2.ss  
EX dll-append_paper.ss 
EX zip_paper_leq.ss 
EX tll.ss 

