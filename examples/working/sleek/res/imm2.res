Starting Reduce... 
Starting Omega...oc
Entail (1): Fail.(may) cause:(failure_code=213)  0<n & 0<m & m1=m & n1=n & (x=null & n=0 | x!=null & 1<=n) & (y=null & m=0 | 
y!=null & 1<=m) |-  y!=x (may-bug).
Entail (2): Valid. 
<1>x::ll<n>@L[Orig][LHSCase] * y::ll<m>@L[Orig][LHSCase] & m1=m & n1=n & {FLOW,(17,18)=__norm}

Entail (3): Fail.(may) cause:ror[15.4 no match for rhs data node: y (may-bug).,15.4 no match for rhs data node: x (may-bug).]
Entail (4): Valid. 
Entail (5): Fail.(may) cause:(failure_code=213)  3<n & (x=null & n=0 | x!=null & 1<=n) & n1=n |-  6<n1 (may-bug).
Stop Omega... 64 invocations 
