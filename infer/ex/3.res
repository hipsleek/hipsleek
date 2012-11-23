Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true & a=inf_a_41 & b=inf_b_42 & c=inf_c_44 & d=inf_d_45 & inf_ann_43<=0 & inf_ann_40<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_41,inf_b_42>@inf_ann_40[Orig]; 
               inf_b_42::node<inf_c_44,inf_d_45>@inf_ann_43[Orig]]
inferred pure: [inf_ann_40<=0; inf_ann_43<=0]

Entail  (2): Valid. 

<1>true & a=inf_a_51 & b=inf_b_52 & inf_ann_50<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_51,inf_b_52>@inf_ann_50[Orig]]
inferred pure: [inf_ann_50<=0]

Entail  (3): Valid. 

<1>true & n=inf_n_57 & inf_ann_56<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_57>@inf_ann_56[Orig][LHSCase]]
inferred pure: [inf_ann_56<=0]

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

<1>true & n=inf_n_126 & inf_ann_125<=0 & inf_n_126<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_126>@inf_ann_125[Orig][LHSCase]]
inferred pure: [inf_n_126<=0; inf_ann_125<=0]

Entail  (11): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (12): Valid. 

<1>EXISTS(q_157,flted_7_155: q_157::ll<flted_7_155>@M[Orig] & flted_7_155+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0]

Entail  (13): Valid. 

<1>EXISTS(flted_7_179: b::ll<flted_7_179>@M[Orig] & flted_7_179+1=n & {FLOW,(17,18)=__norm})
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

Entail  (17): Fail.(may) cause:(failure_code=213)  flted_7_214+1=n & (q_216=null & flted_7_214=0 | q_216!=null & 
1<=flted_7_214) |-  q_216=null (may-bug).


Entail  (18): Valid. 

<1>EXISTS(q_244,flted_7_242: q_244::ll<flted_7_242>@M[Orig] & flted_7_242+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0 | y!=null]

Entail  (19): Valid. 

<1>EXISTS(q_272,flted_7_270: q_272::ll<flted_7_270>@M[Orig] & flted_7_270+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0]

Entail  (20): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (21): Valid. 

<1>EXISTS(flted_7_298: b::ll<flted_7_298>@M[Orig] & flted_7_298+1=n & {FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (22): Valid. 

<1>EXISTS(q_323,flted_7_321: q_323::ll<flted_7_321>@M[Orig] & flted_7_321+1=nn & nn=1 & {FLOW,(17,18)=__norm})
inferred pure: [nn=1; nn!=0]

Entail  (23): Valid. 

<1>y::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (24): Valid. 

<1>EXISTS(flted_7_349: b::ll<flted_7_349>@M[Orig] & flted_7_349+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (25): Fail.(must) cause:15.2 contradiction in RHS: false (must-bug).

<1>true & true & {FLOW,(1,2)=__Error}

Entail  (26): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).


Entail  (27): Fail.(must) cause:(failure_code=213)  m+1=0 & 0<=inf_m_390 |-  inf_m_390=m (must-bug).

<1>true & m+1=0 & a=inf_a_387 & b=inf_b_388 & inf_ann_389<=0 & inf_ann_386<=0 & {FLOW,(1,2)=__Error}
inferred heap: [y::node<inf_a_387,inf_b_388>@inf_ann_386[Orig]; 
               inf_b_388::ll<inf_m_390>@inf_ann_389[Orig][LHSCase]]
inferred pure: [inf_ann_386<=0; inf_ann_389<=0]

Entail  (28): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_409,inf_b_410>@inf_ann_408[Orig]; 
               inf_b_410::ll<inf_m_412>@inf_ann_411[Orig][LHSCase]]
inferred pure: [m!=-1; inf_ann_408<=0; inf_ann_411<=0]

Entail  (29): Valid. 

<1>true & a=inf_a_430 & m=inf_m_434 & inf_ann_433<=0 & inf_ann_429<=0 & b=inf_b_431 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_430,inf_b_431>@inf_ann_429[Orig]; 
               b::ll<inf_m_434>@inf_ann_433[Orig][LHSCase]]
inferred pure: [b=inf_b_431; inf_ann_429<=0; inf_ann_433<=0]

Entail  (30): Valid. 

<1>true & b!=null & a=inf_a_449 & m=inf_m_453 & inf_ann_452<=0 & inf_ann_448<=0 & b=inf_b_450 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_449,inf_b_450>@inf_ann_448[Orig]; 
               b::ll<inf_m_453>@inf_ann_452[Orig][LHSCase]]
inferred pure: [b=inf_b_450; inf_ann_448<=0; inf_ann_452<=0]

Stop Omega... 484 invocations 
