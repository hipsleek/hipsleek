
Processing file "t4-i.ss"
Parsing t4-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... OLD SPECS:  EInfer [x]
   EAssume 1::ref [x]
     true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_14_497,inf_next_14_498>@L[Orig] & true &
       {FLOW,(1,23)=__flow}
         EAssume 1::ref [x]
           true & x=x' & res=inf_val_14_497 & {FLOW,(20,21)=__norm}

Procedure hd0$node SUCCESS
Stop Omega... 33 invocations 
0 false contexts at: ()

Total verification time: 0.384023 second(s)
	Time spent in main process: 0.296018 second(s)
	Time spent in child processes: 0.088005 second(s)
