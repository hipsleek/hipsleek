Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid.
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (2): Valid.
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (3): Fail. (may) cause:(failure_code=213)  true |-  inf_b_78=b (may-bug).

Infer  (4): Valid.
Inferred Heap:[ x::node<inf_Anon_115,inf_b_116>[Orig], y::node<inf_Anon_119,inf_flted_29_120>[Orig]]
Inferred Pure:[ inf_b_116=b & inf_flted_29_120=null]
<1>EXISTS(flted_29_106: true & flted_29_106=1 & b=inf_b_116 & 
inf_flted_29_120=null &
{FLOW,(17,18)=__norm})



ERROR: at File "",Line:0,Col:0 
Message: y is not found in both sides
 exception in Infer  (5) check
: no residue 
Halting Reduce... 
Stop Omega... 90 invocations 
