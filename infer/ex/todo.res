Starting Reduce... 
Starting Omega...oc
Entail  (1): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).
<1>true & true & {FLOW,(1,2)=__Error}

Entail  (2): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Entail  (3): Valid. 
<1>true & b!=null & a=inf_50 & m=inf_53 & inf_b_51=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_53>@M[Orig][LHSCase]; 
               y::node<inf_50,inf_b_51>@M[Orig]]
inferred pure: [inf_b_51=b]

Entail  (4): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [b=null]

Entail  (5): Valid. 
<1>true & c=i & 1<=i & {FLOW,(17,18)=__norm}
inferred pure: [1<=i]

Entail  (6): Valid. 
<1>EXISTS(flted_7_88: b::ll<flted_7_88>@M[Orig] & flted_7_88+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0 | x!=null]

Stop Omega... 96 invocations 
