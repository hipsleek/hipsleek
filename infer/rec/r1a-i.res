
Processing file "r1a-i.ss"
Parsing r1a-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure length$node... OLD SPECS:  EInfer [R]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & R(res,n) & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           true & R(res,n) & 0<=n & {FLOW,(20,21)=__norm}
NEW RELS: [ ( n=0 & res=0) -->  R(res,n), ( (n=1 | 2<=n) & 1<=n & R(res - 1,n - 1)) -->  R(res,n)]

Procedure length$node SUCCESS
Stop Omega... 63 invocations 
0 false contexts at: ()

Total verification time: 0.21 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.02 second(s)
