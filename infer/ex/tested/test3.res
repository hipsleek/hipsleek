Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid.
Inferred Heap:[ y::ll<inf_n_32>[Orig][LHSCase]]
Inferred Pure:[ inf_n_32=0]
<1>true & n=0 & y=x & inf_n_32=0 &
{FLOW,(17,18)=__norm}


Infer  (2): Valid.
Inferred Heap:[]
Inferred Pure:[ aa=a & 1<=a]
<1>EXISTS(flted_13_49: true & a=aa & flted_13_49=null & 1<=aa &
{FLOW,(17,18)=__norm})


Infer  (3): Valid.
Inferred Heap:[ x::ll<inf_n_61>[Orig][LHSCase]]
Inferred Pure:[ inf_n_61=n]
<1>true & n=inf_n_61 & inf_n_61<=(0 - 1) &
{FLOW,(17,18)=__norm}


Infer  (4): Valid.
Inferred Heap:[ q::ll<inf_n_75>[Orig][LHSCase]]
Inferred Pure:[ inf_n_75=n & 1<=n | inf_n_75=n & n<=(0 - 1)]
<1>true & (n=inf_n_75 & 1<=inf_n_75 | n=inf_n_75 & inf_n_75<=(0 - 1)) &
{FLOW,(17,18)=__norm}


Infer  (5): Valid.
<1>EXISTS(flted_23_87: true & flted_23_87=1 & q_88=p & inf_flted_7_99+1=n &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 146 invocations 
