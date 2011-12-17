Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & y=null), n=1]
<1>EXISTS(q_50,flted_7_48: q_50::ll<flted_7_48>@M[Orig] & flted_7_48=0 & 
n=1 &
{FLOW,(17,18)=__norm})


Infer  (2): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_80,flted_7_78: q_80::ll<flted_7_78>@M[Orig] & flted_7_78=0 & 
n=1 &
{FLOW,(17,18)=__norm})


Infer  (3): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_104: b::ll<flted_7_104>@M[Orig] & flted_7_104+1=n &
{FLOW,(17,18)=__norm})


Infer  (4): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>true & n=0 & y=null &
{FLOW,(17,18)=__norm}


Infer  (5): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=1]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=1]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (7): Valid. 
Inferred Heap:[]
Inferred Pure:[ 4<=n]
<1>true & m<n & 4<=n &
{FLOW,(17,18)=__norm}


Infer  (8): Valid. 
Inferred Heap:[]
Inferred Pure:[ 9<=n]
<1>true & 5<=m & m<n & 9<=n &
{FLOW,(17,18)=__norm}


Infer  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1>n]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (10): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(m<n & 1<=n)]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (11): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).
<1>true & true &
{FLOW,(1,2)=__Error}


Infer  (12): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(m=2 & 1<=n)]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (13): Fail.(may) cause:(failure_code=213)  p=a & 3<=m & 4<=a |-  m<a (may-bug).

Infer  (14): Fail.(may) cause:(failure_code=213)  3<=m & 6<=p |-  4<m;  3<=m & 6<=p |-  m<p (may-bug).

Infer  (15): Fail.(may) cause:(failure_code=213)  5<=m |-  m<p (may-bug).

Infer  (16): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m & m<p]
<1>true & 5<=m & m<p &
{FLOW,(17,18)=__norm}


Stop Omega... 244 invocations 
