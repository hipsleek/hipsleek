Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
Inferred Heap:[ y::node<inf_32,inf_b_33>@M[Orig], b::ll<inf_37>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_33=b]
<1>true & b!=null & a=inf_32 & m=inf_37 & inf_b_33=b &
{FLOW,(17,18)=__norm}


Entail  (2): Valid. 
Inferred Heap:[ y::node<inf_53,inf_b_54>@M[Orig], b::ll<inf_58>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_54=b]
<1>true & b!=null & a=inf_53 & m=inf_58 & inf_b_54=b &
{FLOW,(17,18)=__norm}


Entail  (3): Fail.(may) cause:15.4 no match for rhs data node: b (may-bug).

Stop Omega... 77 invocations 
