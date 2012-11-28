Starting Omega...oc

Entail (1) : Fail.(may) cause:UnionR[ true |-  y!=null. LOCS:[0] (may-bug),UnionR[ true |-  y!=null. LOCS:[0] (may-bug), true |-  y!=null. LOCS:[0] (may-bug)]]


Entail (2) : Fail.(must) cause:911 : mismatched annotation


Entail (3) : Valid. 


Entail (4) : Valid. 

 <1>(y::ll<n>@L[Orig][LHSCase] ; x::ll<m>@M[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase]))&0<n & n1=m&{FLOW,(17,18)=__norm}[]


Entail (5) : Valid. 

 <1>(y::ll<n>@L[Orig][LHSCase] ; p::ll<m1>@M[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase]))&0<n & x=null & m2=0&{FLOW,(17,18)=__norm}[]
<2>p::ll<m1>@M[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase])&0<n & x=null & m2=0 & 0<=n&{FLOW,(17,18)=__norm}[]


Entail (6) : Fail.(may) cause:UnionR[ true |-  y!=null. LOCS:[0] (may-bug),UnionR[ true |-  y!=null. LOCS:[0] (may-bug), true |-  y!=null. LOCS:[0] (may-bug)]]

 
Stop Omega... 23 invocations 
