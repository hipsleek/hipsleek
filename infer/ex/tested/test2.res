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
Inferred Heap:[ q::ll<inf_44>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & q!=null & n=inf_44 &
{FLOW,(17,18)=__norm}


Infer  (4): Fail.(may) cause:15.4 no match for rhs data node: q (may-bug).

Infer  (5): Valid. 
Inferred Heap:[ q::ll<inf_n_68>@M[Orig][LHSCase]]
Inferred Pure:[ inf_n_68=0]
<1>true & n=0 & inf_n_68=0 &
{FLOW,(17,18)=__norm}


Infer  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (7): Valid. 
Inferred Heap:[ q::ll<inf_n_98>@M[Orig][LHSCase]]
Inferred Pure:[ inf_n_98=0 & n=0]
<1>true & inf_n_98=0 & n=0 &
{FLOW,(17,18)=__norm}


Infer  (8): Valid. 
Inferred Heap:[ q::ll<inf_n_117>@M[Orig][LHSCase]]
Inferred Pure:[ inf_n_117=0 & n=0]
<1>true & inf_n_117=0 & n=0 &
{FLOW,(17,18)=__norm}


Infer  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Halting Reduce... 
Stop Omega... 101 invocations 
