
Processing file "ll-c.ss"
Parsing ll-c.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           ECase case {
                  n1=1 -> EAssume 1::
                            true & true & {FLOW,(20,21)=__norm} ;
                  n1!=1 -> EAssume 2::
                             true & true & {FLOW,(20,21)=__norm} 
                  }
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         ECase case {
                n1=1 -> EAssume 1::
                          q_530::ll<flted_14_528>@M[Orig] * 
                          x::node<Anon_529,y>@M[Orig] & flted_14_528=0 & 
                          n1=1 & q_530=null & n1=1 & 0<=n1 &
                          {FLOW,(20,21)=__norm}
                ;
                n1!=1 -> EBase true & n1!=0 & {FLOW,(1,23)=__flow}
                                 EAssume 2::
                                   x::node<Anon_553,q_554>@M[Orig] * 
                                   q_554::ll<flted_14_552>@M[Orig] &
                                   (n1=flted_14_552+1 & q_554!=null & 
                                   1<=flted_14_552 | n1=flted_14_552+1 & 
                                   flted_14_552<=(0 - 1) & q_554!=null) & 
                                   n1!=1 & 0<=n1 & {FLOW,(20,21)=__norm}
                
                }

Procedure appif$node~node SUCCESS
Stop Omega... 63 invocations 
2 false contexts at: ( (30,11)  (27,1) )

Total verification time: 0.456027 second(s)
	Time spent in main process: 0.352021 second(s)
	Time spent in child processes: 0.104006 second(s)
