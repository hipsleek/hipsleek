
Processing file "t5-i.ss"
Parsing t5-i.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure tl$node... 
Inferred Heap:[ x::node<inf_val_32_510,inf_next_32_511>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_32_510,inf_next_32_511,x]
Exists Post Vars :[t_22',v_node_33_489']
Initial Residual Post : [ true & t_22'=inf_next_32_511 & v_node_33_489'=t_22' & res=v_node_33_489' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  true & res=inf_next_32_511 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_32_510,inf_next_32_511>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 4::
           true & res=inf_next_32_511 & {FLOW,(20,21)=__norm}

Procedure tl$node SUCCESS
Checking procedure hd$node... 
Inferred Heap:[ x::node<inf_val_24_517,inf_next_24_518>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_val_24_517,inf_next_24_518,x]
Exists Post Vars :[v_int_24_495']
Initial Residual Post : [ true & v_int_24_495'=inf_val_24_517 & res=v_int_24_495' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  true & res=inf_val_24_517 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_val_24_517,inf_next_24_518>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::
           true & res=inf_val_24_517 & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Checking procedure hdtl$node... 
Inferred Heap:[ x::node<inf_inf_val_32_525,inf_inf_next_32_526>@L[Orig], inf_inf_next_32_526::node<inf_inf_val_24_533,inf_inf_next_24_534>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_inf_val_24_533,inf_inf_next_24_534,inf_inf_val_32_525,inf_inf_next_32_526,x]
Exists Post Vars :[inf_val_32_522,inf_next_32_511,inf_next_24_530,inf_val_24_517,v_int_12_499']
Initial Residual Post : [ true & inf_val_32_522=inf_inf_val_32_525 & 
inf_next_32_511=inf_inf_next_32_526 & x'=inf_next_32_511 & 
inf_val_24_517=inf_inf_val_24_533 & inf_next_24_530=inf_inf_next_24_534 & 
v_int_12_499'=inf_val_24_517 & res=v_int_12_499' & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & x'=inf_inf_next_32_526 & res=inf_inf_val_24_533 &
{FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_inf_val_32_525,inf_inf_next_32_526>@L[Orig] * 
       inf_inf_next_32_526::node<inf_inf_val_24_533,inf_inf_next_24_534>@L[Orig] &
       true & {FLOW,(20,21)=__norm}
         EAssume 1::ref [x]
           true & x'=inf_inf_next_32_526 & res=inf_inf_val_24_533 &
           {FLOW,(20,21)=__norm}

Procedure hdtl$node SUCCESS
Stop Omega... 47 invocations 
0 false contexts at: ()

Total verification time: 0.064003 second(s)
	Time spent in main process: 0.044002 second(s)
	Time spent in child processes: 0.020001 second(s)
