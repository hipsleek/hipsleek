
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_16_510,inf_next_16_511>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           true & res=inf_val_16_510 & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Checking procedure tl$node... OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_516,inf_next_33_517>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           true & res=inf_next_33_517 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hdtl$node... OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 2::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_inf_val_33_525,inf_inf_next_33_526>@L[Orig] * 
       inf_inf_next_33_526::node<inf_inf_val_16_533,inf_inf_next_16_534>@L[Orig] &
       true & {FLOW,(20,21)=__norm}
         EAssume 2::ref [x]
           true & x'=inf_inf_next_33_526 & res=inf_inf_val_16_533 &
           {FLOW,(20,21)=__norm}

Procedure hdtl$node SUCCESS
Stop Omega... 51 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.02 second(s)
