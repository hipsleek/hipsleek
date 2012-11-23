Starting Reduce... 
Starting Omega...oc
Entail (1): Valid. 
<1>(x::ll<n>@L[Orig][LHSCase] * y::ll<m>@L[Orig][LHSCase] ; true) & 0<n & m=0 & {FLOW,(17,18)=__norm}

Entail (2): Valid. 
<1>x::ll<n>@L[Orig][LHSCase] * y::ll<m>@L[Orig][LHSCase] & 0<n & 0<m & m1=m & n1=n & {FLOW,(17,18)=__norm}

Entail (3): Fail.(may) cause:(failure_code=213)  0<n & 0<m & (x=null & n=0 | x!=null & 1<=n) & (y=null & m=0 | y!=null & 
1<=m) |-  y!=x (may-bug).

Entail (4): Fail.(may) cause:(failure_code=213)  0<n & 0<m & m1=m & n1=n & (x=null & n=0 | x!=null & 1<=n) & (y=null & m=0 | 
y!=null & 1<=m) |-  y!=x (may-bug).

Entail (5): Fail.(may) cause:(failure_code=213)  m1=m & n1=n & x!=null & y!=null & (x=null & n=0 | x!=null & 1<=n) & 
(y=null & m=0 | y!=null & 1<=m) |-  y!=x (may-bug).

Entail (6): Fail.(may) cause:(failure_code=213)  0<n & n_94=n & (x=null & n=0 | x!=null & 1<=n) & (y=null & n_94=0 | 
y!=null & 1<=n_94) |-  x!=y (may-bug).

Entail (7): Fail.(must) cause:(failure_code=213)  true |-  1=2 (RHS: contradiction).
<1>x::ll<n>@M[Orig][LHSCase] * x::ll<n>@M[Orig][LHSCase] & 0<n & {FLOW,(1,2)=__Error}

Entail (8): Valid. 
Entail (9): Fail.(must) cause:(failure_code=213)  0<=n_126 & 0<n & n_126=n & 0<=n |-  n=0 (must-bug).
Entail (10): Fail.(may) cause:lor[(failure_code=213)  x!=null |-  x=null (must-bug).,valid]
Entail (11): Fail.(may) cause:lor[(failure_code=213)  x!=null |-  x=null (must-bug).,valid]

Stop Omega... 70 invocations 
