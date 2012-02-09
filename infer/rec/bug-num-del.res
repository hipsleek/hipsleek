
Processing file "bug-num-del.ss"
Parsing bug-num-del.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure del$int~int... 
!!! Inferred constraints:[ 2<=n, 1<=n, 1<=n]
Inferred Heap:[]
Inferred Pure:[ 2<=n, 1<=n, 1<=n]

INF-POST-FLAG: true
REL :  B(n,a,res)
POST:  a>=1 & res>=a & res+1=n
PRE :  1<=a & a<n
OLD SPECS:  EInfer [n,B]
   EBase true & true & {FLOW,(20,21)=__norm}
           EBase true & MayLoop & {FLOW,(1,23)=__flow}
                   EAssume 1::
                     true & B(n,a,res) & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<=a & a<n & MayLoop & {FLOW,(1,23)=__flow}
         EAssume 1::
           true & a>=1 & res>=a & res+1=n & {FLOW,(20,21)=__norm}
NEW RELS: [ ( a=1 & res=n - 1 & 2<=n) -->  B(n,a,res), ( (v_int_27_547=res - 1 & v_int_27_543=a - 1 & v_int_27_542=n - 1 & 1<=n & 
2<=a | v_int_27_547=res - 1 & v_int_27_543=a - 1 & v_int_27_542=n - 1 & 
a<=0 & 1<=n) & B(v_int_27_542,v_int_27_543,v_int_27_547)) -->  B(n,a,res)]

Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 109 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.07 second(s)
