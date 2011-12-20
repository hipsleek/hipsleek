Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [1>n]

Entail  (2): Fail.(may) cause:(failure_code=213)  4<=p & 2<m & a=p |-  m<a (may-bug).

Entail  (3): Valid. 
<1>true & 2<m & a=p & b=q & m<p & {FLOW,(17,18)=__norm}
inferred pure: [m<p]

Entail  (4): Fail.(may) cause:(failure_code=213)  2<m & 6<=p |-  4<m;  2<m & 6<=p |-  m<p (may-bug).

Entail  (5): Fail.(may) cause:(failure_code=213)  2<m & 5<=m |-  m<p (may-bug).

Entail  (6): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [3>m]

Entail  (7): Valid. 
<1>true & 2<m & m=p & 5<=m & {FLOW,(17,18)=__norm}
inferred pure: [5<=m]

Entail  (8): Valid. 
<1>true & 2<m & 5<=m & m<p & {FLOW,(17,18)=__norm}
inferred pure: [5<=m & m<p]

Entail  (9): Valid. 
<1>true & 6<m & m<p & {FLOW,(17,18)=__norm}
inferred pure: [m<p]

Entail  (10): Fail.(may) cause:(failure_code=213)  6<m & 8<=p |-  m<p (may-bug).

Entail  (11): Fail.(may) cause:(failure_code=213)  6<m & 8<=p |-  m<p (may-bug).

Entail  (12): Valid. 
<1>true & 6<m & 6<=p & {FLOW,(17,18)=__norm}
inferred pure: [6<=p]

Entail  (13): Fail.(may) cause:(failure_code=213)  6<m & 8<=p |-  z<m;  6<m & 8<=p |-  m<p (may-bug).

Entail  (14): Fail.(may) cause:(failure_code=213)  n!=0 & (1<=inf_n_95 | inf_n_95<=(0 - 1)) & (q=null & inf_n_95=0 | q!=null & 
1<=inf_n_95) |-  inf_n_95=n (may-bug).

Entail  (15): Valid. 
<1>true & n<0 & inf_n_108<=(0 - 1) & {FLOW,(17,18)=__norm}
inferred heap: [x::ll<inf_n_108>@M[Orig][LHSCase]]
inferred pure: [inf_n_108<=(0 - 1)]

Entail  (16): Valid. 
<1>EXISTS(flted_7_130: b::ll<flted_7_130>@M[Orig] & flted_7_130+1=n & {FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (17): Valid. 
<1>EXISTS(flted_7_149: b::ll<flted_7_149>@M[Orig] & flted_7_149+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (18): Valid. 
<1>EXISTS(flted_7_168: b::ll<flted_7_168>@M[Orig] & flted_7_168+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0 | x!=null]

Stop Omega... 322 invocations 
