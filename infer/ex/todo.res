Starting Reduce... 
Starting Omega...oc
Infer  (1): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).
<1>true & true &
{FLOW,(1,2)=__Error}


Infer  (2): Valid. 
Inferred Heap:[ y::node<inf_35,inf_b_36>@M[Orig]]
Inferred Pure:[ a!=inf_35]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (3): Fail.(may) cause:(failure_code=213)  c=i |-  0<c (may-bug).

Halting Reduce... 
Stop Omega... 43 invocations 
