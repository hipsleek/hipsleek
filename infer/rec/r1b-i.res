
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
NEW RELS: [ ( v_int_19_501'=0 & n=0 & res=v_int_19_501') -->  F(res,n), ( (flted_7_533=0 | 1<=flted_7_533) & res=v_int_22_505' & F(m_24',n_538) & 
flted_7_533+1=n & n_538=flted_7_533 & 0<=n_538 & v_int_22_505'=m_24') -->  F(res,n)]

Procedure foo$node SUCCESS
Stop Omega... 62 invocations 
0 false contexts at: ()

Total verification time: 0.228012 second(s)
	Time spent in main process: 0.204012 second(s)
	Time spent in child processes: 0.024 second(s)
