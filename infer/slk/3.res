Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&a=inf_a_41 & b=inf_b_42 & c=inf_c_44 & d=inf_d_45 & inf_ann_43<=1 & inf_ann_40<=1&{FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_41,inf_b_42>@inf_ann_40[Orig]; 
               inf_b_42::node<inf_c_44,inf_d_45>@inf_ann_43[Orig]]
inferred pure: [inf_ann_40<=1; inf_ann_43<=1]

Entail  (2): Valid. 

<1>true&a=inf_a_51 & b=inf_b_52 & inf_ann_50<=0&{FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_51,inf_b_52>@inf_ann_50[Orig]]
inferred pure: [inf_ann_50<=0]

Entail  (3): Valid. 

<1>true&n=inf_n_57 & inf_ann_56<=0&{FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_57>@inf_ann_56[Orig][LHSCase]]
inferred pure: [inf_ann_56<=0]

Entail  (4): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).


Entail  (5): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (6): Valid. 

<1>true&n=0 & y=null&{FLOW,(17,18)=__norm}

Entail  (7): Valid. 

<1>true&y=null & n=0&{FLOW,(17,18)=__norm}

Entail  (8): Fail.(may) cause:15.4 no match for rhs data node: y (may-bug).


Entail  (9): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [n!=1]

Entail  (10): Valid. 

<1>true&n=inf_n_136 & inf_ann_135<=0 & inf_n_136<=0&{FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_136>@inf_ann_135[Orig][LHSCase]]
inferred pure: [inf_n_136<=0; inf_ann_135<=0]

Entail  (11): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (12): Valid. 

<1>EXISTS(q_175,flted_7_173: q_175::ll<flted_7_173>@M[Orig]&flted_7_173+1=n & n=1&{FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0]

Entail  (13): Valid. 

<1>EXISTS(flted_7_197: b::ll<flted_7_197>@M[Orig]&flted_7_197+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (14): Valid. 

<1>y::ll<n>@M[Orig][LHSCase]&n=0&{FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (15): Valid. 

<1>y::ll<n>@M[Orig][LHSCase]&y=null&{FLOW,(17,18)=__norm}
inferred pure: [y=null]

Entail  (16): Valid. 

<1>y::ll<n>@M[Orig][LHSCase]&y=null&{FLOW,(17,18)=__norm}
inferred pure: [y=null]

Entail  (17): Fail.(may) cause:(failure_code=213)  flted_7_239+1=n & (q_241=null & flted_7_239=0 | q_241!=null & 
1<=flted_7_239) |-  q_241=null (may-bug).


Entail  (18): Valid. 

<1>EXISTS(q_273,flted_7_271: q_273::ll<flted_7_271>@M[Orig]&flted_7_271+1=n & n=1&{FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0 | y!=null]

Entail  (19): Valid. 

<1>EXISTS(q_305,flted_7_303: q_305::ll<flted_7_303>@M[Orig]&flted_7_303+1=n & n=1&{FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0]

Entail  (20): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (21): Valid. 

<1>EXISTS(flted_7_331: b::ll<flted_7_331>@M[Orig]&flted_7_331+1=n&{FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (22): Valid. 

<1>EXISTS(q_360,flted_7_358: q_360::ll<flted_7_358>@M[Orig]&flted_7_358+1=nn & nn=1&{FLOW,(17,18)=__norm})
inferred pure: [nn=1; nn!=0]

Entail  (23): Valid. 

<1>y::ll<n>@M[Orig][LHSCase]&n=0&{FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (24): Valid. 

<1>EXISTS(flted_7_387: b::ll<flted_7_387>@M[Orig]&flted_7_387+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (25): Fail.(must) cause:15.2 contradiction in RHS: false (must-bug).

<1>true&true&{FLOW,(1,2)=__Error}

Entail  (26): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).


Entail  (27): Fail.(must) cause:(failure_code=213)  m+1=0 & 0<=inf_m_431 |-  inf_m_431=m (must-bug).

<1>true&m+1=0 & a=inf_a_428 & b=inf_b_429 & inf_ann_430<=0 & inf_ann_427<=0&{FLOW,(1,2)=__Error}
inferred heap: [y::node<inf_a_428,inf_b_429>@inf_ann_427[Orig]; 
               inf_b_429::ll<inf_m_431>@inf_ann_430[Orig][LHSCase]]
inferred pure: [inf_ann_427<=0; inf_ann_430<=0]

Entail  (28): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_453,inf_b_454>@inf_ann_452[Orig]; 
               inf_b_454::ll<inf_m_456>@inf_ann_455[Orig][LHSCase]]
inferred pure: [m!=-1; inf_ann_452<=0; inf_ann_455<=0]

Entail  (29): Valid. 

<1>true&a=inf_a_473 & b=inf_b_474 & m=inf_m_476 & inf_ann_475<=0 & inf_ann_472<=0&{FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_473,inf_b_474>@inf_ann_472[Orig]; 
               inf_b_474::ll<inf_m_476>@inf_ann_475[Orig][LHSCase]]
inferred pure: [inf_ann_472<=0; inf_ann_475<=0]

Entail  (30): Valid. 

<1>true&b!=null & a=inf_a_490 & m=inf_m_494 & inf_ann_493<=0 & inf_ann_489<=0 & b=inf_b_491&{FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_490,inf_b_491>@inf_ann_489[Orig]; 
               b::ll<inf_m_494>@inf_ann_493[Orig][LHSCase]]
inferred pure: [b=inf_b_491; inf_ann_489<=0; inf_ann_493<=0]

Stop Omega... 410 invocations 
