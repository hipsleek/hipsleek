
Processing file "r1b-i.ss"
Parsing r1b-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo$node... OLD SPECS:  EInfer [F]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & F(res,n) & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           true & F(res,n) & 0<=n & {FLOW,(20,21)=__norm}
NEW RELS: [ ( n=0 & res=0) -->  F(res,n), ( (n=1 | 2<=n) & 1<=n & F(res,n - 1)) -->  F(res,n)]

Procedure foo$node SUCCESS
Stop Omega... 62 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.02 second(s)
