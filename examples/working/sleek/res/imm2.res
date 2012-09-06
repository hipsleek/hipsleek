Starting Omega...oc

Entail (1) : Fail.(may) cause: 0<m & 0<n & (y=null & m=0 | y!=null & 1<=m) & (x=null & n=0 | x!=null & 
1<=n) |-  y!=x. LOCS:[0;2;1;8] (may-bug)


Entail (2) : Valid. 

 <1>x::ll<n>@L[Orig][LHSCase] * y::ll<m>@L[Orig][LHSCase]&m1=m & n1=n&{FLOW,(17,18)=__norm}[]


Entail (3) : Fail.(may) cause:UnionR[15.4 no match for rhs data node: y (may-bug).,15.4 no match for rhs data node: x (may-bug).]


Entail (4) : Valid. 


Entail (5) : Fail.(may) cause: (x=null & n1=0 | x!=null & 1<=n1) & 3<n1 |-  6<n1. LOCS:[2;1;29] (may-bug)

Stop Omega... 44 invocations 
