
Processing file "dll-app.ss"
Parsing dll-app.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
Procedure append$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ m!=0, m!=0, m!=0]
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  n>=0 & 1=m & q=r & n+1=t
!!! PRE :  m=1 & 0<=n
!!! NEW RELS:[ (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q),
 (exists(flted_12_840:(t=2 & n=1 | 2+flted_12_840=t & 1+n=t & 3<=t) & r=q & 
  m=1)) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Termination checking result:

Stop Omega... 360 invocations 
0 false contexts at: ()

Total verification time: 0.444026 second(s)
	Time spent in main process: 0.116006 second(s)
	Time spent in child processes: 0.32802 second(s)
