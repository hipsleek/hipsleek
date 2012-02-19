
Processing file "ll-const.ss"
Parsing ll-const.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure foo$node... 
!!! REL :  F(res,n)
!!! POST:  n>=0 & 0=res
!!! PRE :  0<=n
!!! NEW RELS:[ (n=0 & res=0) --> F(res,n),
 (exists(flted_7_533:(n_538=0 & n=1 | flted_7_533=n_538 & -1+n=n_538 & 
  1<=n_538) & F(m_24',n_538) & res=m_24')) --> F(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure foo$node SUCCESS

Termination checking result:

Stop Omega... 90 invocations 
0 false contexts at: ()

Total verification time: 0.116006 second(s)
	Time spent in main process: 0.044002 second(s)
	Time spent in child processes: 0.072004 second(s)
