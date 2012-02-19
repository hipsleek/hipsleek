
Processing file "ll-reverse.ss"
Parsing ll-reverse.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure reverse$node~node... 
!!! REL :  A(m,n,t)
!!! POST:  m>=0 & t>=m & t=n+m
!!! PRE :  0<=m & 0<=n
!!! NEW RELS:[ (t=t_573 & 0<=t_573 & A(m_551,n_550,t_573) & 1<=n & 0<=m & -1+m_551=m & 1+
  n_550=n) --> A(m,n,t),
 (t=m & 0<=m & n=0) --> A(m,n,t)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Termination checking result:

Stop Omega... 149 invocations 
0 false contexts at: ()

Total verification time: 0.180009 second(s)
	Time spent in main process: 0.060003 second(s)
	Time spent in child processes: 0.120006 second(s)
