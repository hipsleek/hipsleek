Starting Reduce... 
Starting Omega...oc
Entail  (1): Fail.(must) cause:(failure_code=213)  true |-  false (RHS: contradiction).

<1>true & 0<n & m<n & {FLOW,(1,2)=__Error}

Entail  (2): Fail.(may) cause:(failure_code=213)  2<m & a=p |-  m<a (may-bug).


Entail  (3): Valid. 

<1>true & 2<m & a=p & b=q & m<p & {FLOW,(17,18)=__norm}
inferred pure: [(1+m)<=p]

Entail  (4): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).


Entail  (5): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).


Entail  (6): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [m<=2]

Entail  (7): Valid. 

<1>true & 2<m & m=p & 5<=m & {FLOW,(17,18)=__norm}
inferred pure: [5<=m]

Entail  (8): Valid. 

<1>true & 2<m & 5<=m & m<p & {FLOW,(17,18)=__norm}
inferred pure: [(1+m)<=p; 5<=m]

Entail  (9): Valid. 

<1>true & 6<m & m<p & {FLOW,(17,18)=__norm}
inferred pure: [(1+m)<=p]

Entail  (10): Fail.(may) cause:(failure_code=213)  6<m |-  m<p (may-bug).


Entail  (11): Fail.(may) cause:(failure_code=213)  6<m |-  5<p;  6<m |-  m<p (may-bug).


Entail  (12): Valid. 

<1>true & 6<m & 6<=p & {FLOW,(17,18)=__norm}
inferred pure: [6<=p]

Entail  (13): Fail.(may) cause:(failure_code=213)  6<m |-  z<m;  6<m |-  m<p (may-bug).


Entail  (14): Fail.(may) cause:(failure_code=213)  n!=0 & (q=null & inf_n_96=0 | q!=null & 1<=inf_n_96) |-  inf_n_96=n (may-bug).


Entail  (15): Fail.(must) cause:(failure_code=213)  n<0 & 0<=inf_n_110 |-  inf_n_110=n (must-bug).

<1>true & n<0 & inf_ann_109<=0 & {FLOW,(1,2)=__Error}
inferred heap: [x::ll<inf_n_110>@inf_ann_109[Orig][LHSCase]]
inferred pure: [inf_ann_109<=0]

Entail  (16): Valid. 

<1>EXISTS(flted_7_132: b::ll<flted_7_132>@M[Orig] & flted_7_132+1=n & {FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (17): Valid. 

<1>EXISTS(flted_7_151: b::ll<flted_7_151>@M[Orig] & flted_7_151+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (18): Valid. 

<1>EXISTS(flted_7_170: b::ll<flted_7_170>@M[Orig] & flted_7_170+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0 | x!=null]

Stop Omega... 259 invocations 
