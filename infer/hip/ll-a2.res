
Processing file "ll-a2.ss"
Parsing ll-a2.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append2$node~node... 
Inferred Heap:[]
Inferred Pure:[ n1!=0, n1!=0, n1!=0, n1!=0]
OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1; n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
         y::ll<n2>@M[Orig][LHSCase] & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             EXISTS(m: x::ll<m>@M[Orig][LHSCase] & m=n2+n1 &
             {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n1; n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
       y::ll<n2>@M[Orig][LHSCase] & n1!=0 & {FLOW,(20,21)=__norm}
         EAssume 1::
           EXISTS(m_591: x::ll<m_591>@M[Orig][LHSCase] & m_591=n2+n1 & 
           0<=n1 & 0<=n2 & {FLOW,(20,21)=__norm})

Procedure append2$node~node SUCCESS
Stop Omega... 76 invocations 
0 false contexts at: ()

Total verification time: 0.108005 second(s)
	Time spent in main process: 0.076004 second(s)
	Time spent in child processes: 0.032001 second(s)
