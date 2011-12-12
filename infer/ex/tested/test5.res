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



ERROR: at File "infer/ex/tested/test5.slk",Line:17,Col:20 
Message: type table does not contain an entry for y' in ; (x node); (a int); (b node)
, could it be an unused var?

 exception in Infer  (3) check
: no residue 
Infer  (4): Valid.
Inferred Heap:[ x::node<inf_Anon_74,inf_b_75>[Orig], y::node<inf_Anon_78,inf_flted_20_79>[Orig]]
Inferred Pure:[ inf_b_75=b & inf_flted_20_79=null]
<1>EXISTS(flted_20_65: true & flted_20_65=1 & b=inf_b_75 & 
inf_flted_20_79=null &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 56 invocations 
