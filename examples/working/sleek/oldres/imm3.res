Starting Reduce... 
Starting Omega...oc
Entail (1): Fail.(may) cause:ror[(failure_code=15.3)  true |-  y!=null (may-bug).,ror[(failure_code=15.3)  true |-  y!=null (may-bug).,(failure_code=15.3)  true |-  y!=null (may-bug).]]
Entail (2): Fail.(may) cause:(failure_code=213)  y=null & n=0 | y!=null & 1<=n |-  y=null (may-bug).
Entail (3): Valid. 
Entail (4): Valid. 
<1>(y::ll<n>@L[Orig][LHSCase] ; x::ll<m>@M[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase])) & 0<n & n1=m & {FLOW,(17,18)=__norm}

Entail (5): Valid. 
<1>(y::ll<n>@L[Orig][LHSCase] ; p::ll<m1>@M[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase])) & 0<n & x=null & m2=0 & {FLOW,(17,18)=__norm}
<2>p::ll<m1>@M[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase]) & 0<n & x=null & m2=0 & 0<=n & {FLOW,(17,18)=__norm}

Entail (6): Valid. 
<1>(x::ll<n>@L[Orig][LHSCase] ; y::ll<m>@I[Orig][LHSCase] * (t::ll<a>@L[Orig][LHSCase] ; z::ll<m>@M[Orig][LHSCase])) & 0<n & a2=a & {FLOW,(17,18)=__norm}

Stop Omega... 40 invocations 
