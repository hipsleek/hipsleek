
Processing file "num-del-a.ss"
Parsing num-del-a.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & res>=a & res+1=n
!!! PRE :  1<=a & a<n
!!! NEW RELS:[ (a=1 & 1+res=n & 2<=n) --> B(n,a,res),
 ((1+v_int_22_542)<=v_int_22_541 & 1<=v_int_22_542 & -1+n=v_int_22_541 & -1+
  a=v_int_22_542 & -1+res=v_int_22_546 & 
  B(v_int_22_541,v_int_22_542,v_int_22_546)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 89 invocations 
0 false contexts at: ()

Total verification time: 0.116006 second(s)
	Time spent in main process: 0.048002 second(s)
	Time spent in child processes: 0.068004 second(s)
