Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid. 
Inferred Heap:[]
Inferred Pure:[ 1>n]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (2): Fail.(may) cause:(failure_code=213)  2<m & a=p |-  m<a (may-bug).

Infer  (3): Fail.(may) cause:(failure_code=213)  3<=m & 6<=p |-  4<m;  3<=m & 6<=p |-  m<p (may-bug).

Infer  (4): Fail.(may) cause:(failure_code=213)  5<=m |-  m<p (may-bug).

Infer  (5): Valid. 
Inferred Heap:[]
Inferred Pure:[ 5<=m & m<p]
<1>true & 5<=m & m<p &
{FLOW,(17,18)=__norm}


Infer  (6): Valid. 
Inferred Heap:[]
Inferred Pure:[ m<p]
<1>true & 7<=m & m<p &
{FLOW,(17,18)=__norm}


Infer  (7): Fail.(may) cause:(failure_code=213)  6<m |-  m<p (may-bug).

Infer  (8): Fail.(may) cause:(failure_code=213)  6<m |-  5<p;  6<m |-  m<p (may-bug).

Infer  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ 6<=p]
<1>true & 7<=m & 6<=p &
{FLOW,(17,18)=__norm}


Infer  (10): Fail.(may) cause:(failure_code=213)  6<m |-  z<m;  6<m |-  m<p (may-bug).

Infer  (11): Fail.(may) cause:(failure_code=213)  (1<=n & 1<=inf_n_80 | n<=(0 - 1) & 1<=inf_n_80 | inf_n_80<=(0 - 1) & 1<=n | 
n<=(0 - 1) & inf_n_80<=(0 - 1)) & (q=null & inf_n_80=0 | q!=null & 
1<=inf_n_80) |-  inf_n_80=n (may-bug).

Infer  (12): Fail.(must) cause:(failure_code=213)  n<0 & 0<=inf_n_99 |-  inf_n_99=n (must-bug).
<1>true & n<0 &
{FLOW,(1,2)=__Error}


Halting Reduce... 
Stop Omega... 233 invocations 
