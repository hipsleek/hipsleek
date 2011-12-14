Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1>n]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (2): Fail.(may) cause:(failure_code=213)  p=a & 3<=m & 4<=a |-  m<a (may-bug).

Infer  (3): Valid. 
Inferred Heap:[]
Inferred Pure:[ m<p]
<1>true & q=b & p=a & 3<=m & m<a &
{FLOW,(17,18)=__norm}


Infer  (4): Fail.(may) cause:(failure_code=213)  3<=m & 6<=p |-  4<m;  3<=m & 6<=p |-  m<p (may-bug).

Infer  (5): Fail.(may) cause:(failure_code=213)  5<=m |-  m<p (may-bug).

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
Inferred Pure:[ m<p]
<1>true & 7<=m & m<p &
{FLOW,(17,18)=__norm}


Infer  (10): Fail.(may) cause:(failure_code=213)  7<=m & 8<=p |-  m<p (may-bug).

Infer  (11): Fail.(may) cause:(failure_code=213)  7<=m & 8<=p |-  m<p (may-bug).

Infer  (12): Valid. 
Inferred Heap:[]
Inferred Pure:[ 6<=p]
<1>true & 7<=m & 6<=p &
{FLOW,(17,18)=__norm}


Infer  (13): Fail.(may) cause:(failure_code=213)  7<=m & 8<=p |-  z<m;  7<=m & 8<=p |-  m<p (may-bug).

Infer  (14): Fail.(may) cause:(failure_code=213)  (1<=n & 1<=inf_n_98 | n<=(0 - 1) & 1<=inf_n_98 | inf_n_98<=(0 - 1) & 1<=n | 
n<=(0 - 1) & inf_n_98<=(0 - 1)) & (q=null & inf_n_98=0 | q!=null & 
1<=inf_n_98) |-  inf_n_98=n (may-bug).

Infer  (15): Valid. 
Inferred Heap:[ x::ll<inf_n_117>@M[Orig][LHSCase]]
Inferred Pure:[ inf_n_117<=(0 - 1)]
<1>true & n<=(0 - 1) & inf_n_117<=(0 - 1) &
{FLOW,(17,18)=__norm}


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
Stop Omega... 318 invocations 
