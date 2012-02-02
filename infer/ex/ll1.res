Starting Reduce... 
Starting Omega...oc
infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_43,inf_v_44,inf_q_45,x]
Entail  (1): Valid. 
<1>true & v=inf_v_44 & q=inf_q_45 & inf_ann_43<=0 & {FLOW,(17,18)=__norm}
inferred heap: [x::node<inf_v_44,inf_q_45>@inf_ann_43[Orig]]
inferred pure: [inf_ann_43<=0]

infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_49,inf_n_50,x]
Entail  (2): Valid. 
<1>true & n=inf_n_50 & inf_ann_49<=0 & {FLOW,(17,18)=__norm}
inferred heap: [x::ll<inf_n_50>@inf_ann_49[Orig][LHSCase]]
inferred pure: [inf_ann_49<=0]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_67,inf_flted_7_68,p]
Entail  (3): Valid. 
<1>true & Anon_61=1 & q_62=p & inf_ann_67<=0 & inf_flted_7_68+1=n & {FLOW,(17,18)=__norm}
inferred heap: [q_62::ll<inf_flted_7_68>@inf_ann_67[Orig]]
inferred pure: [inf_ann_67<=0; p=q_62]

Entail  (4): Valid. 
<1>EXISTS(flted_7_90: p::ll<flted_7_90>@M[Orig] & flted_7_90+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (5): Valid. 
<1>EXISTS(q_115,flted_7_113: q_115::ll<flted_7_113>@M[Orig] & flted_7_113+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (6): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (7): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (8): Valid. 
<1>EXISTS(q_180,flted_7_178: q_180::ll<flted_7_178>@M[Orig] & flted_7_178+1=n & 0<n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1]

Entail  (9): Valid. 
<1>EXISTS(q_209,flted_7_207: q_209::ll<flted_7_207>@M[Orig] & flted_7_207+1=n & n<=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (10): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_262,inf_flted_7_263,p]
Entail  (11): Valid. 
<1>true & Anon_250=1 & Anon_256=3 & q_251=x2 & q_257=p & inf_ann_262<=0 & inf_flted_7_263+1+1=n & {FLOW,(17,18)=__norm}
inferred heap: [q_257::ll<inf_flted_7_263>@inf_ann_262[Orig]]
inferred pure: [inf_ann_262<=0; p=q_257]

Entail  (12): Valid. 
<1>EXISTS(flted_7_287,flted_7_301: p::ll<flted_7_301>@M[Orig] & flted_7_301+1=flted_7_287 & flted_7_287+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=1; n!=0]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_334,inf_flted_7_335,p]
Entail  (13): Valid. 
<1>true & Anon_322=1 & Anon_328=3 & q_323=x2 & q_329=p & inf_ann_334<=0 & inf_flted_7_335+1+1=n & inf_flted_7_335=2 & {FLOW,(17,18)=__norm}
inferred heap: [q_329::ll<inf_flted_7_335>@inf_ann_334[Orig]]
inferred pure: [inf_ann_334<=0; p=q_329; inf_flted_7_335=2]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_355,inf_b_356,inf_q_357,p]
Entail  (14): Valid. 
<1>true & a=1 & x2=p & b=inf_b_356 & q=inf_q_357 & inf_ann_355<=0 & inf_q_357=null & {FLOW,(17,18)=__norm}
inferred heap: [x2::node<inf_b_356,inf_q_357>@inf_ann_355[Orig]]
inferred pure: [inf_ann_355<=0; p=x2; inf_q_357=null]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_377,inf_b_378,inf_q_379,p]
Entail  (15): Fail.(must) cause:(failure_code=213)  flted_53_374=1 |-  flted_53_374=2 (must-bug).
<1>EXISTS(flted_53_374: true & flted_53_374=1 & x2=p & b=inf_b_378 & q=inf_q_379 & inf_ann_377<=0 & {FLOW,(1,2)=__Error})
inferred heap: [x2::node<inf_b_378,inf_q_379>@inf_ann_377[Orig]]
inferred pure: [inf_ann_377<=0; p=x2]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_405,inf_flted_56_406,inf_q_407,p]
Entail  (16): Valid. 
<1>EXISTS(flted_56_401: true & flted_56_401=1 & x2=p & q=inf_q_407 & inf_ann_405<=0 & inf_flted_56_406=3 & inf_q_407=null & {FLOW,(17,18)=__norm})
inferred heap: [x2::node<inf_flted_56_406,inf_q_407>@inf_ann_405[Orig]]
inferred pure: [inf_ann_405<=0; p=x2; inf_flted_56_406=3 & inf_q_407=null]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_433,inf_m_434,p]
Entail  (17): Valid. 
<1>EXISTS(flted_59_430: true & flted_59_430=1 & x2=p & m=inf_m_434 & inf_ann_433<=0 & 4<=inf_m_434 & {FLOW,(17,18)=__norm})
inferred heap: [x2::ll<inf_m_434>@inf_ann_433[Orig][LHSCase]]
inferred pure: [inf_ann_433<=0; p=x2; 4<=inf_m_434]

infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_463,inf_flted_7_464,p]
Entail  (18): Valid. 
<1>EXISTS(flted_62_454: true & flted_62_454=1 & x2=r & Anon_457=a & q_458=p & inf_ann_463<=0 & inf_flted_7_464+1=m & 3<=inf_flted_7_464 & {FLOW,(17,18)=__norm})
inferred heap: [q_458::ll<inf_flted_7_464>@inf_ann_463[Orig]]
inferred pure: [inf_ann_463<=0; p=q_458; 3<=inf_flted_7_464]

Entail  (19): Valid. 
<1>true & m=n & 4<=n & {FLOW,(17,18)=__norm}
inferred pure: [4<=n]

Entail  (20): Valid. 
<1>EXISTS(q_501,flted_7_499: q_501::ll<flted_7_499>@M[Orig] & flted_7_499+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (21): Valid. 
<1>q::ll<m>@M[Orig][LHSCase] & m=0 & {FLOW,(17,18)=__norm}
inferred pure: [m=0]

Entail  (22): Valid. 
<1>true & q=null & {FLOW,(17,18)=__norm}

Entail  (23): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [q=null]

Entail  (24): Valid. 
<1>a::ll<m>@M[Orig][LHSCase] & Anon_24=Anon_23 & m=0 & {FLOW,(17,18)=__norm}
inferred pure: [m=0]

Entail  (25): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x=null]

Entail  (26): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (27): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (28): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x=null]

infer_heap_nodes
infer var: [x]
new infer var: [inf_ann_566,inf_Anon_567,inf_flted_95_568,x]
Entail  (29): Valid. 
<1>true & Anon_27=inf_Anon_567 & inf_ann_566<=0 & inf_flted_95_568=null & {FLOW,(17,18)=__norm}
inferred heap: [x::node<inf_Anon_567,inf_flted_95_568>@inf_ann_566[Orig]]
inferred pure: [inf_ann_566<=0; inf_flted_95_568=null]

Stop Omega... 498 invocations 
