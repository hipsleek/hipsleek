Starting Reduce... 
Starting Omega...oc
infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_40,inf_a_41,inf_b_42,y]
infer_heap_nodes
infer var: [inf_ann_40,inf_a_41,inf_b_42,y]
new infer var: [inf_ann_43,inf_c_44,inf_d_45,inf_ann_40,inf_a_41,inf_b_42,y]
Entail  (1): Valid. 
<1>true & a=inf_a_41 & b=inf_b_42 & c=inf_c_44 & d=inf_d_45 & inf_ann_43<=0 & inf_ann_40<=0 & {FLOW,(17,18)=__norm}
inferred heap: [b::node<inf_c_44,inf_d_45>@inf_ann_43[Orig]; 
               y::node<inf_a_41,inf_b_42>@inf_ann_40[Orig]]
inferred pure: [inf_ann_43<=0; inf_ann_40<=0; inf_b_42=b]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_50,inf_a_51,inf_b_52,y]
Entail  (2): Valid. 
<1>true & a=inf_a_51 & b=inf_b_52 & inf_ann_50<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_51,inf_b_52>@inf_ann_50[Orig]]
inferred pure: [inf_ann_50<=0]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_56,inf_n_57,y]
Entail  (3): Valid. 
<1>true & n=inf_n_57 & inf_ann_56<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_57>@inf_ann_56[Orig][LHSCase]]
inferred pure: [inf_ann_56<=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_64,inf_n_65,n]
Entail  (4): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_75,inf_n_76,n]
Entail  (5): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_86,inf_n_87,n]
Entail  (6): Valid. 
<1>true & n=0 & y=null & {FLOW,(17,18)=__norm}

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_96,inf_n_97,n]
Entail  (7): Valid. 
<1>true & y=null & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_106,inf_n_107,n]
Entail  (8): Fail.(may) cause:15.4 no match for rhs data node: y (may-bug).

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_117,inf_n_118,n]
Entail  (9): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=1]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_125,inf_n_126,y]
Entail  (10): Valid. 
<1>true & n=inf_n_126 & inf_ann_125<=0 & inf_n_126=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_126>@inf_ann_125[Orig][LHSCase]]
inferred pure: [inf_ann_125<=0; inf_n_126=0]

Entail  (11): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (12): Valid. 
<1>EXISTS(q_157,flted_7_155: q_157::ll<flted_7_155>@M[Orig] & flted_7_155+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

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
inferred pure: [n!=0 | y!=null; n=1]

Entail  (19): Valid. 
<1>EXISTS(q_272,flted_7_270: q_272::ll<flted_7_270>@M[Orig] & flted_7_270+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (20): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (21): Valid. 
<1>EXISTS(flted_7_298: b::ll<flted_7_298>@M[Orig] & flted_7_298+1=n & {FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (22): Valid. 
<1>EXISTS(q_323,flted_7_321: q_323::ll<flted_7_321>@M[Orig] & flted_7_321+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (23): Valid. 
<1>y::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (24): Valid. 
<1>EXISTS(flted_7_349: b::ll<flted_7_349>@M[Orig] & flted_7_349+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_358,inf_a_359,inf_b_360,y]
infer_heap_nodes
infer var: [inf_ann_358,inf_a_359,inf_b_360,y]
new infer var: [inf_ann_361,inf_Anon_362,inf_Anon_363,inf_ann_358,inf_a_359,inf_b_360,y]
Entail  (25): Valid. 
<1>true & a=inf_a_359 & b=inf_b_360 & Anon_21=inf_Anon_362 & Anon_22=inf_Anon_363 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_Anon_362,inf_Anon_363>@inf_ann_361[Orig]; 
               y::node<inf_a_359,inf_b_360>@inf_ann_358[Orig]]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_369,inf_a_370,inf_b_371,y]
infer_heap_nodes
infer var: [inf_ann_369,inf_a_370,inf_b_371,y]
new infer var: [inf_ann_372,inf_m_373,inf_ann_369,inf_a_370,inf_b_371,y]
Entail  (26): Valid. 
<1>true & a=inf_a_370 & b=inf_b_371 & m=inf_m_373 & inf_ann_372<=0 & inf_ann_369<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_m_373>@inf_ann_372[Orig][LHSCase]; 
               y::node<inf_a_370,inf_b_371>@inf_ann_369[Orig]]
inferred pure: [inf_ann_372<=0; inf_ann_369<=0]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_384,inf_a_385,inf_b_386,y]
infer_heap_nodes
infer var: [inf_ann_384,inf_a_385,inf_b_386,y]
new infer var: [inf_ann_387,inf_m_388,inf_ann_384,inf_a_385,inf_b_386,y]
Entail  (27): Valid. 
<1>true & m+1=0 & a=inf_a_385 & b=inf_b_386 & inf_ann_387<=0 & inf_ann_384<=0 & inf_m_388=0 - 1 & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_388>@inf_ann_387[Orig][LHSCase]; 
               y::node<inf_a_385,inf_b_386>@inf_ann_384[Orig]]
inferred pure: [inf_ann_387<=0; inf_ann_384<=0; inf_b_386=b; inf_m_388=0 - 1]

infer_heap_nodes
infer var: [y,m]
new infer var: [inf_ann_406,inf_a_407,inf_b_408,y,m]
infer_heap_nodes
infer var: [inf_ann_406,inf_a_407,inf_b_408,y,m]
new infer var: [inf_ann_409,inf_m_410,inf_ann_406,inf_a_407,inf_b_408,y,m]
Entail  (28): Valid. 
<1>true & m+1=0 & a=inf_a_407 & b=inf_b_408 & inf_ann_409<=0 & inf_ann_406<=0 & inf_m_410=0 - 1 & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_410>@inf_ann_409[Orig][LHSCase]; 
               y::node<inf_a_407,inf_b_408>@inf_ann_406[Orig]]
inferred pure: [inf_ann_409<=0; inf_ann_406<=0; inf_b_408=b; inf_m_410=0 - 1]

infer_heap_nodes
infer var: [y,b]
new infer var: [inf_ann_427,inf_a_428,inf_b_429,y,b]
infer_heap_nodes
infer var: [inf_ann_427,inf_a_428,inf_b_429,y,b]
new infer var: [inf_ann_431,inf_m_432,inf_ann_427,inf_a_428,inf_b_429,y,b]
Entail  (29): Valid. 
<1>true & a=inf_a_428 & m=inf_m_432 & inf_ann_431<=0 & inf_ann_427<=0 & inf_b_429=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_432>@inf_ann_431[Orig][LHSCase]; 
               y::node<inf_a_428,inf_b_429>@inf_ann_427[Orig]]
inferred pure: [inf_ann_431<=0; inf_ann_427<=0; inf_b_429=b]

infer_heap_nodes
infer var: [y,b]
new infer var: [inf_ann_446,inf_a_447,inf_b_448,y,b]
infer_heap_nodes
infer var: [inf_ann_446,inf_a_447,inf_b_448,y,b]
new infer var: [inf_ann_450,inf_m_451,inf_ann_446,inf_a_447,inf_b_448,y,b]
Entail  (30): Valid. 
<1>true & b!=null & a=inf_a_447 & m=inf_m_451 & inf_ann_450<=0 & inf_ann_446<=0 & inf_b_448=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_451>@inf_ann_450[Orig][LHSCase]; 
               y::node<inf_a_447,inf_b_448>@inf_ann_446[Orig]]
inferred pure: [inf_ann_450<=0; inf_ann_446<=0; inf_b_448=b]

Stop Omega... 492 invocations 
