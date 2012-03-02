Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (2): Valid. 

<1>EXISTS(flted_7_51: b::ll<flted_7_51>@M[Orig] & flted_7_51+1=n & {FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (3): Valid. 

<1>true & b!=null & a=inf_a_64 & m=inf_m_68 & inf_ann_67<=0 & inf_ann_63<=0 & b=inf_b_65 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_64,inf_b_65>@inf_ann_63[Orig]; 
               b::ll<inf_m_68>@inf_ann_67[Orig][LHSCase]]
inferred pure: [b=inf_b_65; inf_ann_63<=0; inf_ann_67<=0]

Entail  (4): Valid. 

<1>true & b!=null & a=inf_a_83 & m=inf_m_87 & inf_ann_86<=1 & inf_ann_82<=1 & b=inf_b_84 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_83,inf_b_84>@inf_ann_82[Orig]; 
               b::ll<inf_m_87>@inf_ann_86[Orig][LHSCase]]
inferred pure: [b=inf_b_84; inf_ann_82<=1; inf_ann_86<=1]

Entail  (5): Valid. 

<1>true & b!=null & a=inf_a_102 & m=inf_m_106 & inf_ann_105<=0 & inf_ann_101<=0 & b=inf_b_103 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_102,inf_b_103>@inf_ann_101[Orig]; 
               b::ll<inf_m_106>@inf_ann_105[Orig][LHSCase]]
inferred pure: [b=inf_b_103; inf_ann_101<=0; inf_ann_105<=0]

Entail  (6): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).


Entail  (7): Valid. 

<1>EXISTS(flted_7_150,q_166,flted_7_164: q_166::ll<flted_7_164>@M[Orig] & flted_7_164+1=flted_7_150 & flted_7_150+1=n & n=2 & {FLOW,(17,18)=__norm})
inferred pure: [n=2; n!=0; n!=1]

Entail  (8): Fail.(may) cause:lor[15.1 q_198=null & q=q_198 |-  q!=null (must-bug).,valid]


Entail  (9): Valid. 

<1>true & m+1=n & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (10): Valid. 

<1>true & m+1=n & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Stop Omega... 241 invocations 
