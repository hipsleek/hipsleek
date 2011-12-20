Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & b!=null & a=inf_32 & m=inf_35 & inf_b_33=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_35>@M[Orig][LHSCase]; 
               y::node<inf_32,inf_b_33>@M[Orig]]
inferred pure: [inf_b_33=b]

Entail  (2): Valid. 
<1>true & b!=null & a=inf_49 & m=inf_52 & inf_b_50=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_52>@M[Orig][LHSCase]; 
               y::node<inf_49,inf_b_50>@M[Orig]]
inferred pure: [inf_b_50=b]

Entail  (3): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Stop Omega... 86 invocations 
