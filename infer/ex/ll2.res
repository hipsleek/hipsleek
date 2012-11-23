Starting Reduce... 
Starting Omega...oc
infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_58,inf_flted_7_59,p]
infer_heap_nodes
infer var: [p]
new infer var: [inf_ann_81,inf_flted_7_82,p]
Entail  (1): Valid. 
<1>
   true & Anon_52=1 & q_53=p & inf_ann_58<=0 & inf_flted_7_59+1=m &
   {FLOW,(17,18)=__norm}
   or true & Anon_69=1 & Anon_75=2 & q_70=q & q_76=p & inf_ann_81<=0 & 
      inf_flted_7_82+1+1=m & {FLOW,(17,18)=__norm}
   
inferred heap: [q_53::ll<inf_flted_7_59>@inf_ann_58[Orig]; 
               q_76::ll<inf_flted_7_82>@inf_ann_81[Orig]]
inferred pure: [inf_ann_58<=0; p=q_53; inf_ann_81<=0; p=q_76]

Entail  (2): Valid. 
<1>
   EXISTS(flted_7_119,q_135,flted_7_133: q_135::ll<flted_7_133>@M[Orig] &
   flted_7_133+1=flted_7_119 & flted_7_119+1=m & m=2 & {FLOW,(17,18)=__norm})
   or EXISTS(q_159,flted_7_157: q_159::ll<flted_7_157>@M[Orig] & flted_7_157+
      1=m & Anon_14=1 & r=q & m=1 & {FLOW,(17,18)=__norm})
   or p::ll<m>@M[Orig][LHSCase] & Anon_14=Anon_12 & r=t & Anon_15=Anon_13 & 
      m=0 & {FLOW,(17,18)=__norm}
   
inferred pure: [m!=1; m!=0; m=2; m!=0; m=1; m=0]

Entail  (3): Valid. 
<1>EXISTS(q_202,flted_7_200: q_202::ll<flted_7_200>@M[Orig] & flted_7_200+1=n & x!=null & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1; n!=0]

Entail  (4): Valid. 
<1>x::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]
<2>EXISTS(q_231,flted_7_229: q_231::ll<flted_7_229>@M[Orig] & flted_7_229+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (5): Valid. 
<1>x::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}

Entail  (6): Valid. 
<1>x::ll<n>@M[Orig][LHSCase] & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]
<2>EXISTS(q_279,flted_7_277: q_279::ll<flted_7_277>@M[Orig] & flted_7_277+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (7): Valid. 
<1>
   EXISTS(flted_7_309,q_325,flted_7_323: q_325::ll<flted_7_323>@M[Orig] &
   flted_7_323+1=flted_7_309 & flted_7_309+1=n & x!=null & n=2 &
   {FLOW,(17,18)=__norm})
   or x::ll<n>@M[Orig][LHSCase] & x=null & {FLOW,(17,18)=__norm}
   
inferred pure: [n!=1; n=2]

Stop Omega... 241 invocations 
