Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>
   true & Anon_52=1 & q_53=p & inf_flted_7_58+1=m & {FLOW,(17,18)=__norm}
   or true & Anon_68=1 & Anon_74=2 & q_69=q & q_75=p & inf_flted_7_80+1+1=m &
      {FLOW,(17,18)=__norm}
   
inferred heap: [q_53::ll<inf_flted_7_58>@M[Orig]; 
               q_75::ll<inf_flted_7_80>@M[Orig]]
inferred pure: [q_53=p; q_75=p]

Entail  (2): Valid. 
<1>
   EXISTS(flted_7_117,q_133,flted_7_131: q_133::ll<flted_7_131>@M[Orig] &
   flted_7_131+1=flted_7_117 & flted_7_117+1=m & m=2 & {FLOW,(17,18)=__norm})
   or EXISTS(q_157,flted_7_155: q_157::ll<flted_7_155>@M[Orig] & flted_7_155+
      1=m & Anon_14=1 & r=q & m=1 & {FLOW,(17,18)=__norm})
   or p::ll<m>@M[Orig][LHSCase] & Anon_14=Anon_12 & r=t & Anon_15=Anon_13 & 
      m=0 & {FLOW,(17,18)=__norm}
   
inferred pure: [m!=1; m!=0; m=2; m!=0; m=1; m=0]

Entail  (3): Valid. 
<1>EXISTS(q_200,flted_7_198: q_200::ll<flted_7_198>@M[Orig] & flted_7_198+1=n & x!=null & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0]

Entail  (4): Valid. 
<1>x::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]
<2>EXISTS(q_229,flted_7_227: q_229::ll<flted_7_227>@M[Orig] & flted_7_227+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (5): Valid. 
<1>x::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
<2>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (6): Valid. 
<1>x::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]
<2>EXISTS(q_277,flted_7_275: q_277::ll<flted_7_275>@M[Orig] & flted_7_275+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (7): Valid. 
<1>
   EXISTS(flted_7_307,q_323,flted_7_321: q_323::ll<flted_7_321>@M[Orig] &
   flted_7_321+1=flted_7_307 & flted_7_307+1=n & x!=null & n=2 &
   {FLOW,(17,18)=__norm})
   or x::ll<n>@M[Orig][LHSCase] & x=null & {FLOW,(17,18)=__norm}
   
inferred pure: [n!=1; n=2]

Stop Omega... 263 invocations 
