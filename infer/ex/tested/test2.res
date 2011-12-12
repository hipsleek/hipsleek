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


Infer  (4): Fail. (may) cause:15.4 no match for rhs data node: q (may-bug).

Infer  (5): Valid.
Inferred Heap:[ q::ll<inf_n_67>[Orig][LHSCase]]
Inferred Pure:[ inf_n_67=0]
<1>true & n=0 & inf_n_67=0 &
{FLOW,(17,18)=__norm}


Infer  (6): Fail. (may) cause:(failure_code=15.3)  true |-  q!=null;  n=0 |-  n_77=n (may-bug).

Infer  (7): Valid.
Inferred Heap:[ q::ll<inf_n_91>[Orig][LHSCase]]
Inferred Pure:[ inf_n_91=n & 1<=n | inf_n_91=n & n<=(0 - 1)]
<1>true & (n=inf_n_91 & 1<=inf_n_91 | n=inf_n_91 & inf_n_91<=(0 - 1)) &
{FLOW,(17,18)=__norm}


Infer  (8): Fail. (may) cause:(failure_code=15.3)  true |-  q!=null (may-bug).

Halting Reduce... 
Stop Omega... 121 invocations 
