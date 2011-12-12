Starting Reduce... 
Starting Omega...oc
Infer  (1): Fail. (may) cause:may[(failure_code=15.3)  true |-  y!=null (may-bug).,(failure_code=213)  x=null & inf_36=0 | x!=null & 1<=inf_36 |-  x=null (may-bug).]

Infer  (2): Fail. (may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Infer  (3): Valid.
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (4): Valid.
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}



ERROR: at File "infer/ex/tested/test5.slk",Line:23,Col:20 
Message: type table does not contain an entry for y' in ; (x node); (a int); (b node)
, could it be an unused var?

 exception in Infer  (5) check
: no residue 
Infer  (6): Valid.
Inferred Heap:[ x::ll<inf_n_85>[Orig][LHSCase]]
Inferred Pure:[ inf_n_85=n]
<1>true & n=inf_n_85 & inf_n_85<=(0 - 1) &
{FLOW,(17,18)=__norm}


Infer  (7): Valid.
Inferred Heap:[ x::node<inf_Anon_119,inf_b_120>[Orig], y::node<inf_Anon_123,inf_flted_29_124>[Orig]]
Inferred Pure:[ inf_b_120=b & inf_flted_29_124=null]
<1>EXISTS(flted_29_110: true & flted_29_110=1 & b=inf_b_120 & 
inf_flted_29_124=null &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 142 invocations 
