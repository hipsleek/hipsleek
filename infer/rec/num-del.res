
Processing file "num-del.ss"
Parsing num-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure del$int~int... 
Inferred Heap:[]
Inferred Pure:[ 2<=n, 1<=n]

INF-POST-FLAG: false
REL :  B(n,a,res)
POST:  a>=1 & res>=a & res+1=n
PRE :  1<=a & a<n
OLD SPECS:  EInfer [n,B]
   EBase true&true&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     true&B(n,a,res)&{FLOW,(20,21)=__norm}
NEW SPECS:  EBase true&1<=a & a<n & MayLoop&{FLOW,(1,23)=__flow}
         EAssume 1::
           true&B(n,a,res)&{FLOW,(20,21)=__norm}
NEW RELS: [ (a=1 & res=n-1 & 2<=n) --> B(n,a,res), ((v_int_14_544=res-1 & v_int_14_540=a-1 & v_int_14_539=n-1 & 1<=n & 2<=a | 
  v_int_14_544=res-1 & v_int_14_540=a-1 & v_int_14_539=n-1 & a<=0 & 1<=n) & 
  B(v_int_14_539,v_int_14_540,v_int_14_544)) --> B(n,a,res)]

Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 115 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.06 second(s)
