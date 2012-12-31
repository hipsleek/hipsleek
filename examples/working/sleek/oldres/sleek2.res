Starting Reduce... 
Starting Omega...oc
Entail (1): Fail.(must) cause:(failure_code=213)  true |-  1=m & m=2 (RHS: contradiction).
<1>z::node<Anon_54,Anon_53>@M[Orig] * y::ll<Anon_55>@M[Orig][LHSCase] & r_73=null & Anon_72=Anon_11 & 0+1=m & {FLOW,(1,2)=__Error}

Entail (2): Valid. 
<1>z::node<Anon_81,Anon_80>@M[Orig] * y::ll<Anon_82>@M[Orig][LHSCase] & r_103=null & m=1 & Anon_102=Anon_12 & {FLOW,(17,18)=__norm}

Entail (3): Fail.(must) cause:(failure_code=213)  m=0 |-  1=m (must-bug).
<1>z::node<Anon_111,Anon_110>@M[Orig] * y::ll<Anon_112>@M[Orig][LHSCase] & r_133=null & m=0 & Anon_132=Anon_13 & {FLOW,(1,2)=__Error}

Entail (4): Fail.(must) cause:(failure_code=213)  true |-  1=m & m=0 (RHS: contradiction).
<1>EXISTS(flted_24_156: y::ll<flted_24_156>@M[Orig][LHSCase] & r_159=null & flted_24_156=1 & Anon_158=Anon_14 & 0+1=m & {FLOW,(1,2)=__Error})

Entail (5): Valid. 
<1>true & Anon_179=Anon_15 & r_180=r & Anon_185=Anon_16 & r_186=r2 & {FLOW,(17,18)=__norm}

Entail (6): Valid. 
<1>true & Anon_206=Anon_17 & r_207=r & Anon_212=Anon_18 & r_213=r2 & n+1+1=m & {FLOW,(17,18)=__norm}

Entail (7): Valid. 
<1>true & 0<n & m=n & {FLOW,(17,18)=__norm}

Entail (8): Fail.(must) cause:(failure_code=213)  3<n & flted_4_253+1=n & flted_4_267+1=flted_4_253 & (r_269=null & 
flted_4_267=0 | r_269!=null & 1<=flted_4_267) & r2=r_269 |-  r2=null (must-bug).
Stop Omega... 74 invocations 
