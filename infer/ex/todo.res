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


Infer  (3): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1<=i]
<1>true & i=c & 1<=c &
{FLOW,(17,18)=__norm}


Infer  (4): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & x=null) & 0<=n]
<1>EXISTS(flted_7_65: b::ll<flted_7_65>@M[Orig] & flted_7_65+1=n &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 56 invocations 
