Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (2): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (3): Fail.(may) cause:(failure_code=213)  true |-  inf_b_69=b (may-bug).

Entail  (4): Valid. 
<1>true & Anon_18=1 & Anon_17=inf_Anon_113 & Anon_19=inf_Anon_116 & inf_b_114=b & inf_flted_29_117=null & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_Anon_116,inf_flted_29_117>@M[Orig]; 
               x::node<inf_Anon_113,inf_b_114>@M[Orig]]
inferred pure: [inf_b_114=b & inf_flted_29_117=null]


ERROR: at _0_0 
Message: y is not found in both sides
 exception in Entail  (5) check
: no residue 
Stop Omega... 95 invocations 
