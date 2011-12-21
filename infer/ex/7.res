Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1>n]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (2): Fail.(may) cause:(failure_code=213)  4<=p & 2<m & a=p |-  m<a (may-bug).

Entail  (3): Valid. 
Inferred Heap:[]
Inferred Pure:[ m<p]
<1>true & 2<m & a=p & b=q & m<p &
{FLOW,(17,18)=__norm}


Entail  (4): Fail.(may) cause:(failure_code=213)  2<m & 6<=p |-  4<m;  2<m & 6<=p |-  m<p (may-bug).

Entail  (5): Fail.(may) cause:(failure_code=213)  2<m & 5<=m |-  m<p (may-bug).

Entail  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ 3>m]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (7): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m]
<1>true & 2<m & m=p & 5<=m &
{FLOW,(17,18)=__norm}


Entail  (8): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m & m<p]
<1>true & 2<m & 5<=m & m<p &
{FLOW,(17,18)=__norm}


Entail  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ m<p]
<1>true & 6<m & m<p &
{FLOW,(17,18)=__norm}


Entail  (10): Fail.(may) cause:(failure_code=213)  6<m & 8<=p |-  m<p (may-bug).

Entail  (11): Fail.(may) cause:(failure_code=213)  6<m & 8<=p |-  m<p (may-bug).

Entail  (12): Valid. 
Inferred Heap:[]
Inferred Pure:[ 6<=p]
<1>true & 6<m & 6<=p &
{FLOW,(17,18)=__norm}


Entail  (13): Fail.(may) cause:(failure_code=213)  6<m & 8<=p |-  z<m;  6<m & 8<=p |-  m<p (may-bug).

Entail  (14): Fail.(may) cause:(failure_code=213)  n!=0 & (1<=inf_n_95 | inf_n_95<=(0 - 1)) & (q=null & inf_n_95=0 | q!=null & 
1<=inf_n_95) |-  inf_n_95=n (may-bug).

Entail  (15): Valid. 
Inferred Heap:[ x::ll<inf_n_108>@M[Orig][LHSCase]]
Inferred Pure:[ inf_n_108<=(0 - 1)]
<1>true & n<0 & inf_n_108<=(0 - 1) &
{FLOW,(17,18)=__norm}


Entail  (16): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>EXISTS(flted_7_132: b::ll<flted_7_132>@M[Orig] & flted_7_132+1=n &
{FLOW,(17,18)=__norm})


Entail  (17): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_153: b::ll<flted_7_153>@M[Orig] & flted_7_153+1=n &
{FLOW,(17,18)=__norm})


Entail  (18): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & x=null) & 0<=n]
<1>EXISTS(flted_7_174: b::ll<flted_7_174>@M[Orig] & flted_7_174+1=n &
{FLOW,(17,18)=__norm})


Stop Omega... 316 invocations 
