
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
NEW SPECS:  EBase x::node<inf_val_33_520,inf_next_33_521>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           true & res=inf_next_33_521 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hdtl$node... OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 2::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_inf_val_33_534,inf_inf_next_33_535>@L[Orig] * 
       inf_inf_next_33_535::node<inf_inf_val_16_542,inf_inf_next_16_543>@L[Orig] &
       true & {FLOW,(20,21)=__norm}
         EAssume 2::ref [x]
           true & x'=inf_inf_next_33_535 & res=inf_inf_val_16_542 &
           {FLOW,(20,21)=__norm}

Procedure hdtl$node SUCCESS
Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.28 second(s)
	Time spent in main process: 0.26 second(s)
	Time spent in child processes: 0.02 second(s)
