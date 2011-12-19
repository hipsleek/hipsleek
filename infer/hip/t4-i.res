
Processing file "t4-i.ss"
Parsing t4-i.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd0$node... 
Inferred Heap:[ x::node<inf_val_14_497,inf_next_14_498>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_14_497,inf_next_14_498,x]
Exists Post Vars :[v_int_14_486']
Residual Post :  true & x=x' & res=inf_val_14_497 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EAssume 1::ref [x]
     true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EAssume 1::ref [x]
   true & x=x' & res=inf_val_14_497 & {FLOW,(20,21)=__norm}

Procedure hd0$node SUCCESS
Stop Omega... 32 invocations 
0 false contexts at: ()

Total verification time: 0.220012 second(s)
	Time spent in main process: 0.124007 second(s)
	Time spent in child processes: 0.096005 second(s)
