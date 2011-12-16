Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid. 
Inferred Heap:[ y::node<inf_32,inf_b_33>@M[Orig], b::ll<inf_38>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_33=b]
<1>true & inf_32=a & inf_38=m & b=inf_b_33 & inf_b_33!=null &
{FLOW,(17,18)=__norm}


Infer  (2): Valid. 
Inferred Heap:[ y::node<inf_55,inf_b_56>@M[Orig], b::ll<inf_61>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_56=b]
<1>true & inf_55=a & inf_61=m & b=inf_b_56 & inf_b_56!=null &
{FLOW,(17,18)=__norm}


Infer  (3): Fail.(may) cause:15.4 no match for rhs data node: b (may-bug).

Halting Reduce... 
Stop Omega... 88 invocations 
