
Processing file "ll-rev2.ss"
Parsing ll-rev2.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure reverse$node~node... 
!!! REL :  A(xs',m,n,t)
!!! POST:  m>=0 & t>=m & xs'=null & t=n+m
!!! PRE :  0<=m & 0<=n
!!! NEW RELS:[ (exists(xs:t=t_573 & 0<=t_573 & A(xs',m_551,n_550,t_573) & 1<=n & 0<=m & 
  xs!=null & -1+m_551=m & 1+n_550=n)) --> A(xs',m,n,t),
 (t=m & 0<=m & n=0 & xs'=null) --> A(xs',m,n,t)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Termination checking result:

Stop Omega... 147 invocations 
0 false contexts at: ()

Total verification time: 0.164009 second(s)
	Time spent in main process: 0.052003 second(s)
	Time spent in child processes: 0.112006 second(s)
