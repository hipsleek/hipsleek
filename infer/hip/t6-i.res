
Processing file "t6-i.ss"
Parsing t6-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... 
Procedure hd$node SUCCESS
Checking procedure tl$node... 
Procedure tl$node SUCCESS
Checking procedure hdtl$node... OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_Anon_527,inf_528>@L[Orig] * 
       inf_528::node<inf_533,inf_Anon_534>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::ref [x]
           true & x'=inf_528 & res=inf_533 & {FLOW,(20,21)=__norm}

Procedure hdtl$node SUCCESS
Stop Omega... 43 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.01 second(s)
