Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid.
<1>true & q=null & n=0 &
{FLOW,(17,18)=__norm}


Infer  (2): Valid.
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>true & n=0 & q=null &
{FLOW,(17,18)=__norm}


Infer  (3): Valid.
Inferred Heap:[ q::ll<inf_41>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & q!=null & n=inf_41 &
{FLOW,(17,18)=__norm}


Infer  (4): Fail. (may) cause:(failure_code=15.3)  true |-  n_49=n (may-bug).

Infer  (5): Valid.
Inferred Heap:[ q::ll<inf_n_63>[Orig][LHSCase]]
Inferred Pure:[ inf_n_63=0]
<1>true & n=0 & inf_n_63=0 &
{FLOW,(17,18)=__norm}


Infer  (6): Valid.
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (7): Valid.
Inferred Heap:[ q::ll<inf_n_87>[Orig][LHSCase]]
Inferred Pure:[ inf_n_87=0]
<1>true & n=0 & inf_n_87=0 &
{FLOW,(17,18)=__norm}


Infer  (8): Valid.
Inferred Heap:[ q::ll<inf_n_101>[Orig][LHSCase]]
Inferred Pure:[ inf_n_101=0]
<1>true & n=0 & inf_n_101=0 &
{FLOW,(17,18)=__norm}


Infer  (9): Valid.
Inferred Heap:[]
Inferred Pure:[ 1>n & n>(0 - 1)]
<1>false & false &
{FLOW,(17,18)=__norm}


Halting Reduce... 
Stop Omega... 115 invocations 
