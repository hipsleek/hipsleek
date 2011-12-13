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


Infer  (3): Valid.
Inferred Heap:[ x::node<inf_Anon_74,inf_b_75>[Orig], y::node<inf_Anon_78,inf_flted_19_79>[Orig]]
Inferred Pure:[ inf_b_75=b & inf_flted_19_79=null]
<1>EXISTS(flted_19_65: true & flted_19_65=1 & b=inf_b_75 & 
inf_flted_19_79=null &
{FLOW,(17,18)=__norm})


Infer  (4): Valid.
Inferred Heap:[ x::node<inf_Anon_111,inf_b_112>[Orig], y::node<inf_Anon_115,inf_flted_29_116>[Orig]]
Inferred Pure:[ inf_b_112=b & inf_flted_29_116=null]
<1>EXISTS(flted_29_102: true & flted_29_102=1 & b=inf_b_112 & 
inf_flted_29_116=null &
{FLOW,(17,18)=__norm})



ERROR: at File "",Line:0,Col:0 
Message: y is not found in both sides
 exception in Infer  (5) check
: no residue 
Halting Reduce... 
Stop Omega... 73 invocations 
