
Processing file "ll-b.ss"
Parsing ll-b.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & n1!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           
           q_528::ll<flted_14_526>@M[Orig] * x::node<Anon_527,y>@M[Orig] &
           n1=flted_14_526+1 & q_528=null & 0<=n1 & {FLOW,(20,21)=__norm}
           or x::node<Anon_527,q_528>@M[Orig] * 
              q_528::ll<flted_14_526>@M[Orig] & n1=flted_14_526+1 & 
              q_528!=null & 0<=n1 & {FLOW,(20,21)=__norm}
           

Procedure appif$node~node SUCCESS
Stop Omega... 56 invocations 
0 false contexts at: ()

Total verification time: 0.408024 second(s)
	Time spent in main process: 0.320019 second(s)
	Time spent in child processes: 0.088005 second(s)
