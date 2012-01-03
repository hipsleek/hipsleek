
Processing file "ll-b.ss"
Parsing ll-b.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... 
Inferred Heap:[]
Inferred Pure:[ n1!=0, n1!=0, n1!=0, n1!=0]
Pre Vars :[x,y,n1]
Exists Post Vars :[v_bool_25_504']
Initial Residual Post : [ q_530::ll<flted_14_528>@M[Orig] * x::node<Anon_529,y>@M[Orig] &
flted_14_528+1=n1 & q_530=null & v_bool_25_504' & q_530=null & 
v_bool_25_504' & {FLOW,(20,21)=__norm}, x::node<Anon_529,q_530>@M[Orig] * q_530::ll<flted_14_528>@M[Orig] &
flted_14_528+1=n1 & q_530!=null & 133::!(v_bool_25_504') & q_530!=null & 
!(v_bool_25_504') & {FLOW,(20,21)=__norm}]
Final Residual Post :  
 q_530::ll<flted_14_528>@M[Orig] * x::node<Anon_529,y>@M[Orig] &
 n1=flted_14_528+1 & q_530=null & {FLOW,(20,21)=__norm}
 or x::node<Anon_529,q_530>@M[Orig] * q_530::ll<flted_14_528>@M[Orig] &
    n1=flted_14_528+1 & q_530!=null & {FLOW,(20,21)=__norm}
 
OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & n1!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           
           q_530::ll<flted_14_528>@M[Orig] * x::node<Anon_529,y>@M[Orig] &
           n1=flted_14_528+1 & q_530=null & 0<=n1 & {FLOW,(20,21)=__norm}
           or x::node<Anon_529,q_530>@M[Orig] * 
              q_530::ll<flted_14_528>@M[Orig] & n1=flted_14_528+1 & 
              q_530!=null & 0<=n1 & {FLOW,(20,21)=__norm}
           

Procedure appif$node~node SUCCESS
Stop Omega... 54 invocations 
0 false contexts at: ()

Total verification time: 0.064002 second(s)
	Time spent in main process: 0.044002 second(s)
	Time spent in child processes: 0.02 second(s)
