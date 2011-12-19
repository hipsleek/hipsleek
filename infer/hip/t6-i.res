
Processing file "t6-i.ss"
Parsing t6-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hdtl$node... 
Inferred Heap:[ x::node<inf_Anon_518,inf_519>@L[Orig], inf_519::node<inf_524,inf_Anon_525>@L[Orig]]
Inferred Pure:[]
Pre Vars :[inf_524,inf_Anon_525,inf_Anon_518,inf_519,x]
Exists Post Vars :[Anon_12,b,Anon_11,a,v_int_27_489']
Initial Residual Post : [ true & Anon_12=inf_Anon_518 & b=inf_519 & x'=b & a=inf_524 & 
Anon_11=inf_Anon_525 & v_int_27_489'=a & res=v_int_27_489' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  true & x'=inf_519 & res=inf_524 & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [x]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 3::ref [x]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase x::node<inf_Anon_518,inf_519>@L[Orig] * 
       inf_519::node<inf_524,inf_Anon_525>@L[Orig] & true &
       {FLOW,(20,21)=__norm}
         EAssume 3::ref [x]
           true & x'=inf_519 & res=inf_524 & {FLOW,(20,21)=__norm}

Procedure hdtl$node SUCCESS
Checking procedure tl$node... 
Procedure tl$node SUCCESS
Checking procedure hd$node... 
Procedure hd$node SUCCESS
Stop Omega... 41 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.23 second(s)
	Time spent in child processes: 0.02 second(s)
