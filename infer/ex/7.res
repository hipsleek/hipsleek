Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1>n]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (2): Fail.(may) cause:(failure_code=213)  2<m & a=p |-  m<a (may-bug).

Infer  (3): Valid. 
Inferred Heap:[]
Inferred Pure:[ m<p]
<1>true & q=b & p=a & 3<=m & m<a &
{FLOW,(17,18)=__norm}


Infer  (4): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).

Infer  (5): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).

Infer  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ 3>m]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (7): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m]
<1>true & m=p & 5<=p &
{FLOW,(17,18)=__norm}


Infer  (8): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m & m<p]
<1>true & 5<=m & m<p &
{FLOW,(17,18)=__norm}


Infer  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m & m<p]
<1>true & 7<=m & m<p &
{FLOW,(17,18)=__norm}


Infer  (10): Fail.(may) cause:(failure_code=213)  6<m |-  m<p (may-bug).

Infer  (11): Fail.(may) cause:(failure_code=213)  6<m |-  5<p;  6<m |-  m<p (may-bug).

Infer  (12): Fail.(may) cause:(failure_code=213)  true |-  6<=p;  true |-  5<p (may-bug).

Infer  (13): Fail.(may) cause:(failure_code=213)  6<m |-  z<m;  6<m |-  m<p (may-bug).

Infer  (14): Fail.(may) cause:(failure_code=213)  n!=0 & (q=null & inf_n_98=0 | q!=null & 1<=inf_n_98) |-  inf_n_98=n (may-bug).

Infer  (15): Fail.(must) cause:(failure_code=213)  n<0 & 0<=inf_n_117 |-  inf_n_117=n (must-bug).
<1>true & n<0 &
{FLOW,(1,2)=__Error}


Infer  (16): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>EXISTS(flted_7_144: b::ll<flted_7_144>@M[Orig] & flted_7_144+1=n &
{FLOW,(17,18)=__norm})


Infer  (17): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_165: b::ll<flted_7_165>@M[Orig] & flted_7_165+1=n &
{FLOW,(17,18)=__norm})


Infer  (18): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & x=null) & 0<=n]
<1>EXISTS(flted_7_186: b::ll<flted_7_186>@M[Orig] & flted_7_186+1=n &
{FLOW,(17,18)=__norm})


Halting Reduce... 
Stop Omega... 353 invocations 
