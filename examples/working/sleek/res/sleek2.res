Starting Omega...oc

Entail (1) : Fail.(must) cause: true |-  1+0=m & m=2. LOCS:[0;4;15] (RHS: contradiction)

 <1>z::node<Anon_57,Anon_56>@M[Orig] * y::ll<Anon_12>@M[Orig][LHSCase]&r_75=null & Anon_74=Anon_11 & 0+1=m&{FLOW,(1,2)=__Error}[]


Entail (2) : Valid. 

 <1>z::node<Anon_83,Anon_82>@M[Orig] * y::ll<Anon_14>@M[Orig][LHSCase]&r_104=null & m=1 & Anon_103=Anon_13&{FLOW,(17,18)=__norm}[]


Entail (3) : Fail.(must) cause: m=0 |-  1+0=m. LOCS:[23;4] (must-bug)

 <1>z::node<Anon_112,Anon_111>@M[Orig] * y::ll<Anon_16>@M[Orig][LHSCase]&r_133=null & m=0 & Anon_132=Anon_15&{FLOW,(1,2)=__Error}[]


Entail (4) : Fail.(must) cause: true |-  1+0=m & m=0. LOCS:[0;4;27] (RHS: contradiction)

 <1>EXISTS(flted_27_156: y::ll<flted_27_156>@M[Orig][LHSCase]&r_159=null & flted_27_156=1 & Anon_158=Anon_17 & 0+1=m&{FLOW,(1,2)=__Error})[]


Entail (5) : Valid. 

 <1>true&Anon_179=Anon_18 & r_180=r & Anon_185=Anon_19 & r_186=r2&{FLOW,(17,18)=__norm}[]


Entail (6) : Valid. 

 <1>true&Anon_204=Anon_20 & r_205=r & Anon_210=Anon_21 & r_211=r2 & n+1+1=m&{FLOW,(17,18)=__norm}[]


Entail (7) : Valid. 

 <1>true&0<n & m=n&{FLOW,(17,18)=__norm}[]


Entail (8) : Fail.(must) cause: 3<(flted_4_261+1+1) & (r2=null & flted_4_261=0 | r2!=null & 1<=flted_4_261) |-  r2=null. LOCS:[4;3;1;0;43] (must-bug)

Stop Omega... 56 invocations 
