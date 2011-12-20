
Processing file "ll-c.ss"
Parsing ll-c.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... Pre Vars :[x,y,n1]
Exists Post Vars :[v_bool_27_506']
Initial Residual Post : [ q_530::ll<flted_14_528>@M[Orig] * x::node<Anon_529,y>@M[Orig] &
flted_14_528+1=n1 & n1=1 & q_530=null & v_bool_27_506' & q_530=null & 
v_bool_27_506' & {FLOW,(20,21)=__norm}]
Final Residual Post :  q_530::ll<flted_14_528>@M[Orig] * x::node<Anon_529,y>@M[Orig] &
flted_14_528=0 & n1=1 & q_530=null & {FLOW,(20,21)=__norm}

Inferred Heap:[]
Inferred Pure:[ n1!=0 | n1=1, n1!=0 | n1=1]
Pre Vars :[x,y,n1]
Exists Post Vars :[v_bool_27_506']
Initial Residual Post : [ x::node<Anon_555,q_556>@M[Orig] * q_556::ll<flted_14_554>@M[Orig] &
flted_14_554+1=n1 & n1!=1 & q_556!=null & 159::!(v_bool_27_506') & 
q_556!=null & !(v_bool_27_506') & {FLOW,(20,21)=__norm}]
Final Residual Post :  x::node<Anon_555,q_556>@M[Orig] * q_556::ll<flted_14_554>@M[Orig] &
(n1=flted_14_554+1 & q_556!=null & 1<=flted_14_554 | n1=flted_14_554+1 & 
flted_14_554<=(0 - 1) & q_556!=null) & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           ECase case {
                  n1=1 -> EAssume 1::
                            true & true & {FLOW,(20,21)=__norm} ;
                  n1!=1 -> EAssume 2::
                             true & true & {FLOW,(20,21)=__norm} 
                  }
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         ECase case {
                n1=1 -> EAssume 1::
                          q_530::ll<flted_14_528>@M[Orig] * 
                          x::node<Anon_529,y>@M[Orig] & flted_14_528=0 & 
                          n1=1 & q_530=null & n1=1 & 0<=n1 &
                          {FLOW,(20,21)=__norm}
                ;
                n1!=1 -> EBase true & (n1!=0 | n1=1) & {FLOW,(1,23)=__flow}
                                 EAssume 2::
                                   x::node<Anon_555,q_556>@M[Orig] * 
                                   q_556::ll<flted_14_554>@M[Orig] &
                                   (n1=flted_14_554+1 & q_556!=null & 
                                   1<=flted_14_554 | n1=flted_14_554+1 & 
                                   flted_14_554<=(0 - 1) & q_556!=null) & 
                                   n1!=1 & 0<=n1 & {FLOW,(20,21)=__norm}
                
                }

Procedure appif$node~node SUCCESS
Stop Omega... 61 invocations 
2 false contexts at: ( (30,11)  (27,1) )

Total verification time: 0.068003 second(s)
	Time spent in main process: 0.044002 second(s)
	Time spent in child processes: 0.024001 second(s)
