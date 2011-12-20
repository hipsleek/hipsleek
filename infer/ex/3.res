Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & a=inf_40 & b=inf_41 & c=inf_42 & d=inf_43 & {FLOW,(17,18)=__norm}
inferred heap: [b::node<inf_42,inf_43>@M[Orig]; 
               y::node<inf_40,inf_41>@M[Orig]]
inferred pure: [b=inf_41]

Entail  (2): Valid. 
<1>true & a=inf_48 & b=inf_49 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_48,inf_49>@M[Orig]]

Entail  (3): Valid. 
<1>true & n=inf_53 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_53>@M[Orig][LHSCase]]

Entail  (4): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Entail  (5): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (6): Valid. 
<1>true & n=0 & y=null & {FLOW,(17,18)=__norm}

Entail  (7): Valid. 
<1>true & y=null & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (8): Fail.(may) cause:15.4 no match for rhs data node: y (may-bug).

Entail  (9): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=1]

Entail  (10): Valid. 
<1>true & n=inf_115 & inf_115=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_115>@M[Orig][LHSCase]]
inferred pure: [inf_115=0]

Entail  (11): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (12): Valid. 
<1>EXISTS(q_146,flted_7_144: q_146::ll<flted_7_144>@M[Orig] & flted_7_144+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (13): Valid. 
<1>EXISTS(flted_7_168: b::ll<flted_7_168>@M[Orig] & flted_7_168+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (14): Valid. 
<1>y::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (15): Valid. 
<1>y::ll<n>@M[Orig][LHSCase] & y=null & {FLOW,(17,18)=__norm}
inferred pure: [y=null]

Entail  (16): Valid. 
<1>y::ll<n>@M[Orig][LHSCase] & y=null & {FLOW,(17,18)=__norm}
inferred pure: [y=null]

Entail  (17): Fail.(may) cause:(failure_code=213)  flted_7_203+1=n & (q_205=null & flted_7_203=0 | q_205!=null & 
1<=flted_7_203) |-  q_205=null (may-bug).

Entail  (18): Valid. 
<1>EXISTS(q_233,flted_7_231: q_233::ll<flted_7_231>@M[Orig] & flted_7_231+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0 | y!=null; n=1]

Entail  (19): Valid. 
<1>EXISTS(q_261,flted_7_259: q_261::ll<flted_7_259>@M[Orig] & flted_7_259+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (20): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (21): Valid. 
<1>EXISTS(flted_7_287: b::ll<flted_7_287>@M[Orig] & flted_7_287+1=n & {FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (22): Valid. 
<1>EXISTS(q_312,flted_7_310: q_312::ll<flted_7_310>@M[Orig] & flted_7_310+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (23): Valid. 
<1>y::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (24): Valid. 
<1>EXISTS(flted_7_338: b::ll<flted_7_338>@M[Orig] & flted_7_338+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (25): Valid. 
<1>true & a=inf_347 & b=inf_348 & Anon_21=inf_Anon_349 & Anon_22=inf_Anon_350 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_Anon_349,inf_Anon_350>@M[Orig]; 
               y::node<inf_347,inf_348>@M[Orig]]

Entail  (26): Valid. 
<1>true & a=inf_356 & b=inf_357 & m=inf_358 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_358>@M[Orig][LHSCase]; 
               y::node<inf_356,inf_357>@M[Orig]]

Entail  (27): Valid. 
<1>true & m+1=0 & a=inf_369 & b=inf_370 & inf_m_371=0 - 1 & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_371>@M[Orig][LHSCase]; 
               y::node<inf_369,inf_370>@M[Orig]]
inferred pure: [b=inf_370; inf_m_371=0 - 1]

Entail  (28): Valid. 
<1>true & m+1=0 & a=inf_389 & b=inf_390 & inf_m_391=0 - 1 & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_391>@M[Orig][LHSCase]; 
               y::node<inf_389,inf_390>@M[Orig]]
inferred pure: [b=inf_390; inf_m_391=0 - 1]

Entail  (29): Valid. 
<1>true & a=inf_408 & m=inf_411 & inf_b_409=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_411>@M[Orig][LHSCase]; 
               y::node<inf_408,inf_b_409>@M[Orig]]
inferred pure: [inf_b_409=b]

Entail  (30): Valid. 
<1>true & b!=null & a=inf_425 & m=inf_428 & inf_b_426=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_428>@M[Orig][LHSCase]; 
               y::node<inf_425,inf_b_426>@M[Orig]]
inferred pure: [inf_b_426=b]

Stop Omega... 410 invocations 
