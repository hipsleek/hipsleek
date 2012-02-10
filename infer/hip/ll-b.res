
Processing file "ll-b.ss"
Parsing ll-b.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... 
Inferred Heap:[]
Inferred Pure:[ n1!=0, n1!=0]
OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     true&true&{FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&(1<=n1 | n1<=(0-1)) & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   
                   x::node<Anon_527,y>@M[Orig]&q_528=null & 0<=n1&
                   {FLOW,(20,21)=__norm}
                   or x::node<Anon_527,q_528>@M[Orig]&q_528!=null & 0<=n1&
                      {FLOW,(20,21)=__norm}
                   
NEW RELS: []

Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 61 invocations 
0 false contexts at: ()

Total verification time: 0.17 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.02 second(s)
