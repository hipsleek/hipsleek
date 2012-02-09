Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>x::ll<n>@L[Orig][LHSCase] & x=null & rs=t & t=0 & {FLOW,(17,18)=__norm}
inferred rel: [( n=0 & rs=0) -->  R(rs,n)]

Entail  (2): Valid. 

<1>x::node<Anon_12,q>@L[Orig] * q::ll<m>@L[Orig][LHSCase] & m+1=n & x!=null & rs=r+1 & R(r,m) & {FLOW,(17,18)=__norm}
inferred rel: [( r=rs - 1 & m=n - 1 & 1<=n & R(r,m)) -->  R(rs,n)]

Stop Omega... 23 invocations 
