
Processing file "dll-del.ss"
Parsing dll-del.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure delete$node2~int... 
!!! REL :  B(m,n)
!!! POST:  m>=1 & m+1=n
!!! PRE :  2<=n
!!! NEW RELS:[ (exists(flted_12_600:m=2 & n=3 | -1+n=m & flted_12_600=m & 3<=m)) --> B(m,n),
 (n=2 & m=1) --> B(m,n),
 (1+m_800=m & 1<=m & B(m_800,n_734) & 1+n_734=n & exists(a:(1+a)<=n & 
  2<=a)) --> B(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Termination checking result:

Stop Omega... 195 invocations 
0 false contexts at: ()

Total verification time: 0.244014 second(s)
	Time spent in main process: 0.088005 second(s)
	Time spent in child processes: 0.156009 second(s)
