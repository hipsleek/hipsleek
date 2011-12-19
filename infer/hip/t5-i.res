
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... 
Inferred Heap:[ x::node<inf_val_16_510,inf_next_16_511>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_16_510,inf_next_16_511,x]
Exists Post Vars :[v_int_16_499']
Initial Residual Post : [ true & v_int_16_499'=inf_val_16_510 & res=v_int_16_499' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  true & res=inf_val_16_510 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_16_510,inf_next_16_511>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           true & res=inf_val_16_510 & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Checking procedure tl$node... 
Inferred Heap:[ x::node<inf_val_33_516,inf_next_33_517>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_33_516,inf_next_33_517,x]
Exists Post Vars :[t_22',v_node_34_489']
Initial Residual Post : [ true & t_22'=inf_next_33_517 & v_node_34_489'=t_22' & res=v_node_34_489' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  true & res=inf_next_33_517 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_33_516,inf_next_33_517>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           true & res=inf_next_33_517 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hdtl$node... 
Inferred Heap:[ x::node<inf_inf_val_33_525,inf_inf_next_33_526>@L[Orig], inf_inf_next_33_526::node<inf_inf_val_16_533,inf_inf_next_16_534>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_inf_val_16_533,inf_inf_next_16_534,inf_inf_val_33_525,inf_inf_next_33_526,x]
Exists Post Vars :[inf_val_33_522,inf_next_33_517,inf_next_16_530,inf_val_16_510,v_int_25_493']
Initial Residual Post : [ true & inf_val_33_522=inf_inf_val_33_525 & 
inf_next_33_517=inf_inf_next_33_526 & x'=inf_next_33_517 & 
inf_val_16_510=inf_inf_val_16_533 & inf_next_16_530=inf_inf_next_16_534 & 
v_int_25_493'=inf_val_16_510 & res=v_int_25_493' & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & x'=inf_inf_next_33_526 & res=inf_inf_val_16_533 &
{FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
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
Stop Omega... 47 invocations 
0 false contexts at: ()

Total verification time: 0.320019 second(s)
	Time spent in main process: 0.17601 second(s)
	Time spent in child processes: 0.144009 second(s)
