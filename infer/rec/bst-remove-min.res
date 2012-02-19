
Processing file "bst-remove-min.ss"
Parsing bst-remove-min.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure remove_min$node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(s,res,s1)
!!! POST:  res>=s & s1>=res
!!! PRE :  true
!!! NEW RELS:[ (res<=s1 & exists(pl_578:s<=pl_578 & pl_578<=res) & 
  exists(b:s1<=b)) --> A(s,res,s1),
 (A(s_600,tmp_33',s1_628) & s1=s1_628 & 
  exists(qs_579:exists(b_30:exists(lg_577:s_600=s & 
  exists(v_580:qs_579<=b_30 & lg_577=b_30 & exists(b_601:v_580<=qs_579 & 
  s<=b_601 & s1_628<=b_601 & b_601<=v_580))))) & tmp_33'=res) --> A(s,res,s1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Termination checking result:

Stop Omega... 178 invocations 
0 false contexts at: ()

Total verification time: 1.216074 second(s)
	Time spent in main process: 0.072004 second(s)
	Time spent in child processes: 1.14407 second(s)
