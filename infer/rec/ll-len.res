
Processing file "ll-len.ss"
Parsing ll-len.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure length$node... 
FIXPOINT:  res>=0 & res=n
OLD SPECS:  EInfer [R]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & R(res,n) & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           true & n=res & 0<=res & 0<=n & {FLOW,(20,21)=__norm}
NEW RELS: [ ( n=0 & res=0) -->  R(res,n), ( R(r_24',n_539) & 0<=n_539 & -1+res=r_24' & (n=1 | 2<=n) & 1+n_539=n) -->  R(res,n)]

Procedure length$node SUCCESS
Stop Omega... 68 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.04 second(s)
