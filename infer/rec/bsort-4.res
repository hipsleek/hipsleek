
Processing file "bsort-4.ss"
Parsing bsort-4.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure bubble$node... 
!!! REL :  A(res)
!!! POST:  !(res)
!!! PRE :  true
!!! NEW RELS:[ (tmp_42' & 1<=res & A(tmp_42')) --> A(res),
 (A(tmp_42') & 1<=res & tmp_42') --> A(res),
 (res<=0) --> A(res),
 (!(tmp_42') & res<=0 & A(tmp_42')) --> A(res),
 (A(tmp_42') & res<=0 & !(tmp_42')) --> A(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure bubble$node SUCCESS

Termination checking result:

Stop Omega... 549 invocations 
0 false contexts at: ()

Total verification time: 0.996061 second(s)
	Time spent in main process: 0.272016 second(s)
	Time spent in child processes: 0.724045 second(s)
