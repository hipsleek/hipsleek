
Processing file "ll-c.ss"
Parsing ll-c.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... 
Inferred Heap:[]
Inferred Pure:[ n1!=0]
OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           ECase case {
                  n1=1 -> EBase true&MayLoop&{FLOW,(1,23)=__flow}
                                  EAssume 1::
                                    true&true&{FLOW,(20,21)=__norm}
                  ;
                  n1!=1 -> EBase true&MayLoop&{FLOW,(1,23)=__flow}
                                   EAssume 2::
                                     true&true&{FLOW,(20,21)=__norm}
                  
                  }
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         ECase case {
                n1=1 -> EBase true&MayLoop&{FLOW,(1,23)=__flow}
                                EAssume 1::
                                  x::node<Anon_529,y>@M[Orig]&n1=1 & n1=1 & 
                                  0<=n1&{FLOW,(20,21)=__norm}
                ;
                n1!=1 -> EBase true&(1<=n1 | n1<=(0-1)) & MayLoop&
                               {FLOW,(1,23)=__flow}
                                 EAssume 2::
                                   x::node<Anon_553,q_554>@M[Orig]&
                                   (q_554!=null & 2<=n1 | n1<=0 & 
                                   q_554!=null) & n1!=1 & 0<=n1&
                                   {FLOW,(20,21)=__norm}
                
                }
NEW RELS: []

Procedure appif$node~node SUCCESS

Termination checking result:

Stop Omega... 68 invocations 
2 false contexts at: ( (30,11)  (27,1) )

Total verification time: 0.2 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.02 second(s)
