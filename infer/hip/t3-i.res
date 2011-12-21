
Processing file "t3-i.ss"
Parsing t3-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x::node<v_530,q_532>@M[Orig] * 
           q_532::llf<Anon_533,flted_8_531>@M[Orig] & n=flted_8_531+1 & 
           v_530=v & res=v & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Stop Omega... 61 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.02 second(s)
