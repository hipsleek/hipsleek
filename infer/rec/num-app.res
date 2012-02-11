
Processing file "num-app.ss"
Parsing num-app.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appN$int~int... 
Inferred Heap:[]
Inferred Pure:[ 1<=n, 1<=n]

INF-POST-FLAG: true
REL :  A(n,m,res)
POST:  n>=1 & n+m=res
PRE :  1<=n
OLD SPECS:  EInfer [n,m,A]
   EBase true&true&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     true&A(n,m,res)&{FLOW,(20,21)=__norm}
NEW SPECS:  EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}
         EAssume 1::
           true&n>=1 & n+m=res&{FLOW,(20,21)=__norm}
NEW RELS: [ (n=1 & res=m+1) --> A(n,m,res), (res=v_int_12_526+1 & n=v_int_12_522+1 & 1<=v_int_12_522 & 
  A(v_int_12_522,m,v_int_12_526)) --> A(n,m,res)]

Procedure appN$int~int SUCCESS

Termination checking result:

Stop Omega... 98 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.05 second(s)
