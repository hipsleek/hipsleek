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



ERROR: at File "infer/ex/tested/test5.slk",Line:18,Col:20 
Message: type table does not contain an entry for y' in ; (x node); (a int); (b node)
, could it be an unused var?

 exception in Infer  (3) check
: no residue 
Infer  (4): Valid.
Inferred Heap:[ x::node<inf_Anon_77,inf_b_78>[Orig], y::node<inf_Anon_81,inf_flted_22_82>[Orig]]
Inferred Pure:[ inf_b_78=b & inf_flted_22_82=null]
<1>EXISTS(flted_22_68: true & flted_22_68=1 & b=inf_b_78 & 
inf_flted_22_82=null &
{FLOW,(17,18)=__norm})


Infer  (5): Valid.
Inferred Heap:[ x::node<inf_Anon_114,inf_b_115>[Orig], y::node<inf_Anon_118,inf_flted_30_119>[Orig]]
Inferred Pure:[ inf_b_115=b & inf_flted_30_119=null]
<1>EXISTS(flted_30_105: true & flted_30_105=1 & b=inf_b_115 & 
inf_flted_30_119=null &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 76 invocations 
