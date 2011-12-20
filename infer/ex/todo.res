Starting Reduce... 
Starting Omega...oc
Entail  (1): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).
<1>true & true &
{FLOW,(1,2)=__Error}


Entail  (2): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Entail  (3): Valid. 
Inferred Heap:[ y::node<inf_50,inf_b_51>@M[Orig], b::ll<inf_53>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_51=b]
<1>true & b!=null & a=inf_50 & m=inf_53 & inf_b_51=b &
{FLOW,(17,18)=__norm}


Entail  (4): Valid. 
Inferred Heap:[]
Inferred Pure:[ b=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (5): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1<=i]
<1>true & c=i & 1<=i &
{FLOW,(17,18)=__norm}


Entail  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & x=null) & 0<=n]
<1>EXISTS(flted_7_90: b::ll<flted_7_90>@M[Orig] & flted_7_90+1=n &
{FLOW,(17,18)=__norm})


Stop Omega... 97 invocations 
