Starting Reduce... 
Starting Omega...oc
Infer  (1): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).
<1>true & true &
{FLOW,(1,2)=__Error}


Infer  (2): Fail.(may) cause:15.4 no match for rhs data node: b (may-bug).

Infer  (3): Valid. 
Inferred Heap:[ y::node<inf_51,inf_b_52>@M[Orig], b::ll<inf_57>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_b_52 & inf_b_52!=null]
<1>true & inf_51=a & inf_57=m & inf_b_52=b & b!=null &
{FLOW,(17,18)=__norm}


Infer  (4): Valid. 
Inferred Heap:[]
Inferred Pure:[ b=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (5): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1<=i]
<1>true & i=c & 1<=c &
{FLOW,(17,18)=__norm}


Infer  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & x=null) & 0<=n]
<1>EXISTS(flted_7_97: b::ll<flted_7_97>@M[Orig] & flted_7_97+1=n &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 89 invocations 
