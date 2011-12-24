
Processing file "ll-a2.ss"
Parsing ll-a2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append2$node~node... OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1; n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
         y::ll<n2>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             EXISTS(m: x::ll<m>@M[Orig][LHSCase] & m=n2+n1 &
             {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n1; n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
       y::ll<n2>@M[Orig][LHSCase] & n1!=0 & {FLOW,(20,21)=__norm}
         EAssume 1::
           EXISTS(m_589: x::ll<m_589>@M[Orig][LHSCase] & m_589=n2+n1 & 
           0<=n1 & 0<=n2 & {FLOW,(20,21)=__norm})

Procedure append2$node~node SUCCESS
Stop Omega... 107 invocations 
0 false contexts at: ()

Total verification time: 0.58 second(s)
	Time spent in main process: 0.55 second(s)
	Time spent in child processes: 0.03 second(s)
