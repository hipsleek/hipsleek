
Processing file "t3-i.ss"
Parsing t3-i.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure hd$node... 
Inferred Heap:[]
Inferred Pure:[ n!=0]
Pre Vars :[v,x,n]
Exists Post Vars :[v_int_21_504']
Initial Residual Post : [ x::node<v_532,q_534>@M[Orig] * q_534::llf<Anon_535,flted_8_533>@M[Orig] &
flted_8_533+1=n & v_532=v & v_int_21_504'=v_532 & res=v_int_21_504' &
{FLOW,(20,21)=__norm}]
Final Residual Post :  x::node<v_532,q_534>@M[Orig] * q_534::llf<Anon_535,flted_8_533>@M[Orig] &
n=flted_8_533+1 & v_532=v & res=v & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [n]
   EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[v; n](ex)x::llf<v,n>@M[Orig][LHSCase] & n!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x::node<v_532,q_534>@M[Orig] * 
           q_534::llf<Anon_535,flted_8_533>@M[Orig] & n=flted_8_533+1 & 
           v_532=v & res=v & 0<=n & {FLOW,(20,21)=__norm}

Procedure hd$node SUCCESS
Stop Omega... 45 invocations 
0 false contexts at: ()

Total verification time: 0.068003 second(s)
	Time spent in main process: 0.044002 second(s)
	Time spent in child processes: 0.024001 second(s)
