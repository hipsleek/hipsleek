Starting Reduce... 
Starting Omega...oc

@1! lhs_xpure_orig: a=p & b=q & x!=null
@1! lhs_xpure0: a=p & b=q & x!=null
@1! lhs_rels:None
@1! xp: true
@1! lhs(orig): : true
@1! lhs0(orig): : a=p & b=q & x!=null
@1! rhs(orig): : v<:@I
@1! lhs (after filter_ante): : true
@1! fml: : v<:@I
@1! total_sub_flag:false
@1! vars overlap:[]
@1! quan_var: :[]
@1! lhs_xpure: : true
@1! lhs_xpure(w ann): : 0<=v & v<=2
@1! new_p_assume: : 3<=v | v<=1
@1! rhs_xpure: : v<:@I
@1! fml2: : v<=1
@1! new_p2: : v<=1
@1! quan_var: :[]
@1! iv: :[v]
@1! new_p1: : 3<=v | v<=1
@1! new_p2: : v<=1
@1! new_p2 (pairwisecheck): : v<=1
infer_pure_m@1
infer_pure_m@1 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=1),0)
Entail  (1): Valid. 

<1>true&a=p & b=q & v<=1&{FLOW,(17,18)=__norm}
inferred pure: [v<=1]


@2! lhs_xpure_orig: a=p & b=q & x!=null
@2! lhs_xpure0: a=p & b=q & x!=null
@2! lhs_rels:None
@2! xp: true
@2! lhs(orig): : true
@2! lhs0(orig): : a=p & b=q & x!=null
@2! rhs(orig): : v<:@M
@2! lhs (after filter_ante): : true
@2! fml: : v<:@M
@2! total_sub_flag:false
@2! vars overlap:[]
@2! quan_var: :[]
@2! lhs_xpure: : true
@2! lhs_xpure(w ann): : 0<=v & v<=2
@2! new_p_assume: : 3<=v | v<=0
@2! rhs_xpure: : v<:@M
@2! fml2: : v<=0
@2! new_p2: : v<=0
@2! quan_var: :[]
@2! iv: :[v]
@2! new_p1: : 3<=v | v<=0
@2! new_p2: : v<=0
@2! new_p2 (pairwisecheck): : v<=0
infer_pure_m@2
infer_pure_m@2 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=0),0)
Entail  (2): Valid. 

<1>true&a=p & b=q & v<=0&{FLOW,(17,18)=__norm}
inferred pure: [v<=0]


@3! lhs_xpure_orig: flted_7_70+1=n & a=Anon_71 & b=q_72 & (q_72=null & flted_7_70=0 | 
q_72!=null & 1<=flted_7_70) & x!=null
@3! lhs_xpure0: flted_7_70+1=n & a=Anon_71 & b=q_72 & 0<=flted_7_70 & x!=null
@3! lhs_rels:None
@3! xp: true
@3! lhs(orig): : true
@3! lhs0(orig): : flted_7_70+1=n & a=Anon_71 & b=q_72 & 0<=flted_7_70 & x!=null
@3! rhs(orig): : v<:@M
@3! lhs (after filter_ante): : true
@3! fml: : v<:@M
@3! total_sub_flag:true
@3! vars overlap:[]
@3! quan_var: :[]
@3! lhs_xpure: : true
@3! lhs_xpure(w ann): : 0<=v & v<=2
@3! new_p_assume: : 3<=v | v<=0
@3! rhs_xpure: : v<:@M
@3! fml2: : v<=0
@3! new_p2: : v<=0
@3! quan_var: :[]
@3! iv: :[x,v]
@3! new_p1: : 3<=v | v<=0
@3! new_p2: : v<=0
@3! new_p2 (pairwisecheck): : v<=0
infer_pure_m@3
infer_pure_m@3 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=0),0)
Entail  (3): Valid. 

<1>EXISTS(flted_7_70: b::ll<flted_7_70>@v[Orig]&flted_7_70+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=0]


@4! lhs_xpure_orig: flted_7_90+1=n & a=Anon_91 & b=q_92 & (q_92=null & flted_7_90=0 | 
q_92!=null & 1<=flted_7_90) & x!=null
@4! lhs_xpure0: flted_7_90+1=n & a=Anon_91 & b=q_92 & 0<=flted_7_90 & x!=null
@4! lhs_rels:None
@4! xp: true
@4! lhs(orig): : true
@4! lhs0(orig): : flted_7_90+1=n & a=Anon_91 & b=q_92 & 0<=flted_7_90 & x!=null
@4! rhs(orig): : v<:@I
@4! lhs (after filter_ante): : true
@4! fml: : v<:@I
@4! total_sub_flag:true
@4! vars overlap:[]
@4! quan_var: :[]
@4! lhs_xpure: : true
@4! lhs_xpure(w ann): : 0<=v & v<=2
@4! new_p_assume: : 3<=v | v<=1
@4! rhs_xpure: : v<:@I
@4! fml2: : v<=1
@4! new_p2: : v<=1
@4! quan_var: :[]
@4! iv: :[x,v]
@4! new_p1: : 3<=v | v<=1
@4! new_p2: : v<=1
@4! new_p2 (pairwisecheck): : v<=1
infer_pure_m@4
infer_pure_m@4 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=1),0)
Entail  (4): Valid. 

<1>EXISTS(flted_7_90: b::ll<flted_7_90>@v[Orig]&flted_7_90+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=1]


@5! lhs_xpure_orig: flted_7_110+1=n & a=Anon_111 & b=q_112 & (q_112=null & flted_7_110=0 | 
q_112!=null & 1<=flted_7_110) & x!=null
@5! lhs_xpure0: flted_7_110+1=n & a=Anon_111 & b=q_112 & 0<=flted_7_110 & x!=null
@5! lhs_rels:None
@5! xp: true
@5! lhs(orig): : true
@5! lhs0(orig): : flted_7_110+1=n & a=Anon_111 & b=q_112 & 0<=flted_7_110 & x!=null
@5! rhs(orig): : v<:@I
@5! lhs (after filter_ante): : true
@5! fml: : v<:@I
@5! total_sub_flag:true
@5! vars overlap:[]
@5! quan_var: :[]
@5! lhs_xpure: : true
@5! lhs_xpure(w ann): : 0<=v & v<=2
@5! new_p_assume: : 3<=v | v<=1
@5! rhs_xpure: : v<:@I
@5! fml2: : v<=1
@5! new_p2: : v<=1
@5! quan_var: :[]
@5! iv: :[n,v]
@5! new_p1: : 3<=v | v<=1
@5! new_p2: : v<=1
@5! new_p2 (pairwisecheck): : v<=1
infer_pure_m@5
infer_pure_m@5 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=1),0)
Entail  (5): Valid. 

<1>EXISTS(flted_7_110: b::ll<flted_7_110>@v[Orig]&flted_7_110+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=1]


@6! lhs_xpure_orig: flted_7_130+1=n & a=Anon_131 & b=q_132 & (q_132=null & flted_7_130=0 | 
q_132!=null & 1<=flted_7_130) & x!=null
@6! lhs_xpure0: flted_7_130+1=n & a=Anon_131 & b=q_132 & 0<=flted_7_130 & x!=null
@6! lhs_rels:None
@6! xp: true
@6! lhs(orig): : true
@6! lhs0(orig): : flted_7_130+1=n & a=Anon_131 & b=q_132 & 0<=flted_7_130 & x!=null
@6! rhs(orig): : v<:@M
@6! lhs (after filter_ante): : true
@6! fml: : v<:@M
@6! total_sub_flag:true
@6! vars overlap:[]
@6! quan_var: :[]
@6! lhs_xpure: : true
@6! lhs_xpure(w ann): : 0<=v & v<=2
@6! new_p_assume: : 3<=v | v<=0
@6! rhs_xpure: : v<:@M
@6! fml2: : v<=0
@6! new_p2: : v<=0
@6! quan_var: :[]
@6! iv: :[n,v]
@6! new_p1: : 3<=v | v<=0
@6! new_p2: : v<=0
@6! new_p2 (pairwisecheck): : v<=0
infer_pure_m@6
infer_pure_m@6 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=0),0)
Entail  (6): Valid. 

<1>EXISTS(flted_7_130: b::ll<flted_7_130>@v[Orig]&flted_7_130+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=0]

Entail  (7): Valid. 

<1>EXISTS(flted_7_151: x::node<a,b>@v[Orig] * b::ll<flted_7_151>@v[Orig]&flted_7_151+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (8): Valid. 

<1>EXISTS(flted_7_171: b::ll<flted_7_171>@M[Orig]&flted_7_171+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (9): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(flted_7_194,q_214,flted_7_212: Hole[197] * q_214::ll<flted_7_212>@L[Orig]&flted_7_212+1=flted_7_194 & flted_7_194+1=n & 1<n&{FLOW,(17,18)=__norm})


@7! lhs_xpure_orig: flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & a=Anon_237 & b=q_238 & 
Anon_14=Anon_251 & Anon_15=q_252 & (q_252=null & flted_7_250=0 | 
q_252!=null & 1<=flted_7_250) & q_238!=null & x!=null
@7! lhs_xpure0: flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & a=Anon_237 & b=q_238 & 
Anon_14=Anon_251 & Anon_15=q_252 & 0<=flted_7_250 & q_238!=null & x!=null
@7! lhs_rels:None
@7! xp: true
@7! lhs(orig): : true
@7! lhs0(orig): : flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & a=Anon_237 & b=q_238 & 
Anon_14=Anon_251 & Anon_15=q_252 & 0<=flted_7_250 & q_238!=null & x!=null
@7! rhs(orig): : v1<:v2
@7! lhs (after filter_ante): : true
@7! fml: : v1<:v2
@7! total_sub_flag:false
@7! vars overlap:[]
@7! quan_var: :[]
@7! lhs_xpure: : true
@7! lhs_xpure(w ann): : 0<=v1 & v1<=2 & 0<=v2 & v2<=2
@7! new_p_assume: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | v1<=v2
@7! rhs_xpure: : v1<:v2
@7! fml2: : v1<=v2
@7! new_p2: : v1<=v2
@7! quan_var: :[]
@7! iv: :[v1,v2]
@7! new_p1: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | v1<=v2
@7! new_p2: : v1<=v2
@7! new_p2 (pairwisecheck): : v1<=v2
infer_pure_m@7
infer_pure_m@7 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=v2),0)

@8! lhs_xpure_orig: flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & a=Anon_237 & b=q_238 & 
Anon_14=Anon_251 & Anon_15=q_252 & v1<=v2 & (q_252=null & flted_7_250=0 | 
q_252!=null & 1<=flted_7_250) & q_238!=null & x!=null
@8! lhs_xpure0: flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & a=Anon_237 & b=q_238 & 
Anon_14=Anon_251 & Anon_15=q_252 & v1<=v2 & 0<=flted_7_250 & q_238!=null & 
x!=null
@8! lhs_rels:None
@8! xp: v1<=v2
@8! lhs(orig): : v1<=v2
@8! lhs0(orig): : flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & a=Anon_237 & b=q_238 & 
Anon_14=Anon_251 & Anon_15=q_252 & v1<=v2 & 0<=flted_7_250 & q_238!=null & 
x!=null
@8! rhs(orig): : v1<:@I
@8! lhs (after filter_ante): : v1<=v2
@8! fml: : v1<=v2 & v1<:@I
@8! total_sub_flag:true
@8! vars overlap:[v1]
@8! quan_var: :[]
@8! lhs_xpure: : v1<=v2
@8! lhs_xpure(w ann): : 0<=v2 & v2<=2 & 0<=v1 & v1<=2 & v1<=v2
@8! new_p_assume: : v2<v1 | v1<=v2 & 3<=v2 | v1<=1
@8! rhs_xpure: : v1<:@I
@8! fml2: : v1<=v2 & v1<=1
@8! new_p2: : v1<=v2 & v1<=1
@8! quan_var: :[]
@8! iv: :[v1,v2]
@8! new_p1: : v2<v1 | v1<=v2 & 3<=v2 | v1<=1
@8! new_p2: : v1<=1
@8! new_p2 (pairwisecheck): : v1<=1
infer_pure_m@8
infer_pure_m@8 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=1),0)
Entail  (10): Valid. 

<1>EXISTS(flted_7_236,flted_7_250: Anon_15::ll<flted_7_250>@v1[Orig]&flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & v1<=v2 & v1<=1&{FLOW,(17,18)=__norm})
inferred pure: [v1<=1; v1<=v2]


@9! lhs_xpure_orig: flted_7_287+1=flted_7_273 & flted_7_273+1=n & 1<n & a=Anon_274 & b=q_275 & 
Anon_16=Anon_288 & Anon_17=q_289 & (q_289=null & flted_7_287=0 | 
q_289!=null & 1<=flted_7_287) & q_275!=null & x!=null
@9! lhs_xpure0: flted_7_287+1=flted_7_273 & flted_7_273+1=n & 1<n & a=Anon_274 & b=q_275 & 
Anon_16=Anon_288 & Anon_17=q_289 & 0<=flted_7_287 & q_275!=null & x!=null
@9! lhs_rels:None
@9! xp: true
@9! lhs(orig): : true
@9! lhs0(orig): : flted_7_287+1=flted_7_273 & flted_7_273+1=n & 1<n & a=Anon_274 & b=q_275 & 
Anon_16=Anon_288 & Anon_17=q_289 & 0<=flted_7_287 & q_275!=null & x!=null
@9! rhs(orig): : @I<:v2
@9! lhs (after filter_ante): : true
@9! fml: : @I<:v2
@9! total_sub_flag:false
@9! vars overlap:[]
@9! quan_var: :[]
@9! lhs_xpure: : true
@9! lhs_xpure(w ann): : 0<=v2 & v2<=2
@9! new_p_assume: : v2<=(0-1) | 1<=v2
@9! rhs_xpure: : @I<:v2
@9! fml2: : 1<=v2
@9! new_p2: : 1<=v2
@9! quan_var: :[]
@9! iv: :[v2]
@9! new_p1: : v2<=(0-1) | 1<=v2
@9! new_p2: : 1<=v2
@9! new_p2 (pairwisecheck): : 1<=v2
infer_pure_m@9
infer_pure_m@9 EXIT out :(new es,inf pure,rel_ass) :(None,Some( 1<=v2),0)
Entail  (11): Valid. 

<1>EXISTS(flted_7_273,flted_7_287: Anon_17::ll<flted_7_287>@I[Orig]&flted_7_287+1=flted_7_273 & flted_7_273+1=n & 1<n & 1<=v2&{FLOW,(17,18)=__norm})
inferred pure: [1<=v2]


@10! lhs_xpure_orig: c=a & d=b & x!=null
@10! lhs_xpure0: c=a & d=b & x!=null
@10! lhs_rels:None
@10! xp: true
@10! lhs(orig): : true
@10! lhs0(orig): : c=a & d=b & x!=null
@10! rhs(orig): : v1<:v2
@10! lhs (after filter_ante): : true
@10! fml: : v1<:v2
@10! total_sub_flag:false
@10! vars overlap:[]
@10! quan_var: :[]
@10! lhs_xpure: : true
@10! lhs_xpure(w ann): : 0<=v1 & v1<=2 & 0<=v2 & v2<=2
@10! new_p_assume: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | v1<=v2
@10! rhs_xpure: : v1<:v2
@10! fml2: : v1<=v2
@10! new_p2: : v1<=v2
@10! quan_var: :[]
@10! iv: :[v1,v2]
@10! new_p1: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | v1<=v2
@10! new_p2: : v1<=v2
@10! new_p2 (pairwisecheck): : v1<=v2
infer_pure_m@10
infer_pure_m@10 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=v2),0)
Entail  (12): Valid. 

<1>true&c=a & d=b & v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2]


@11! lhs_xpure_orig: x=null & n=0 | x!=null & 1<=n
@11! lhs_xpure0: 0<=n
@11! lhs_rels:None
@11! xp: true
@11! lhs(orig): : true
@11! lhs0(orig): : 0<=n
@11! rhs(orig): : v1<:v2
@11! lhs (after filter_ante): : true
@11! fml: : v1<:v2
@11! total_sub_flag:false
@11! vars overlap:[]
@11! quan_var: :[]
@11! lhs_xpure: : true
@11! lhs_xpure(w ann): : 0<=v1 & v1<=2 & 0<=v2 & v2<=2
@11! new_p_assume: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | v1<=v2
@11! rhs_xpure: : v1<:v2
@11! fml2: : v1<=v2
@11! new_p2: : v1<=v2
@11! quan_var: :[]
@11! iv: :[v1,v2]
@11! new_p1: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | v1<=v2
@11! new_p2: : v1<=v2
@11! new_p2 (pairwisecheck): : v1<=v2
infer_pure_m@11
infer_pure_m@11 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=v2),0)

infer_pure_m@12
infer_pure_m@12 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (13): Valid. 

<1>true&v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2]


@13! lhs_xpure_orig: x=null & n=0 | x!=null & 1<=n
@13! lhs_xpure0: 0<=n
@13! lhs_rels:None
@13! xp: true
@13! lhs(orig): : true
@13! lhs0(orig): : 0<=n
@13! rhs(orig): : @I<:v2
@13! lhs (after filter_ante): : true
@13! fml: : @I<:v2
@13! total_sub_flag:false
@13! vars overlap:[]
@13! quan_var: :[]
@13! lhs_xpure: : true
@13! lhs_xpure(w ann): : 0<=v2 & v2<=2
@13! new_p_assume: : v2<=(0-1) | 1<=v2
@13! rhs_xpure: : @I<:v2
@13! fml2: : 1<=v2
@13! new_p2: : 1<=v2
@13! quan_var: :[]
@13! iv: :[v2]
@13! new_p1: : v2<=(0-1) | 1<=v2
@13! new_p2: : 1<=v2
@13! new_p2 (pairwisecheck): : 1<=v2
infer_pure_m@13
infer_pure_m@13 EXIT out :(new es,inf pure,rel_ass) :(None,Some( 1<=v2),0)

infer_pure_m@14
infer_pure_m@14 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (14): Valid. 

<1>true&1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [1<=v2]


@15! lhs_xpure_orig: x=null & n=0 | x!=null & 1<=n
@15! lhs_xpure0: 0<=n
@15! lhs_rels:None
@15! xp: true
@15! lhs(orig): : true
@15! lhs0(orig): : 0<=n
@15! rhs(orig): : v2<:@I
@15! lhs (after filter_ante): : true
@15! fml: : v2<:@I
@15! total_sub_flag:false
@15! vars overlap:[]
@15! quan_var: :[]
@15! lhs_xpure: : true
@15! lhs_xpure(w ann): : 0<=v2 & v2<=2
@15! new_p_assume: : 3<=v2 | v2<=1
@15! rhs_xpure: : v2<:@I
@15! fml2: : v2<=1
@15! new_p2: : v2<=1
@15! quan_var: :[]
@15! iv: :[v2]
@15! new_p1: : 3<=v2 | v2<=1
@15! new_p2: : v2<=1
@15! new_p2 (pairwisecheck): : v2<=1
infer_pure_m@15
infer_pure_m@15 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v2<=1),0)

infer_pure_m@16
infer_pure_m@16 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (15): Valid. 

<1>true&v2<=1&{FLOW,(17,18)=__norm}
inferred pure: [v2<=1]


@17! lhs_xpure_orig: x=null & n=0 | x!=null & 1<=n
@17! lhs_xpure0: 0<=n
@17! lhs_rels:None
@17! xp: true
@17! lhs(orig): : true
@17! lhs0(orig): : 0<=n
@17! rhs(orig): : v2<:@M
@17! lhs (after filter_ante): : true
@17! fml: : v2<:@M
@17! total_sub_flag:false
@17! vars overlap:[]
@17! quan_var: :[]
@17! lhs_xpure: : true
@17! lhs_xpure(w ann): : 0<=v2 & v2<=2
@17! new_p_assume: : 3<=v2 | v2<=0
@17! rhs_xpure: : v2<:@M
@17! fml2: : v2<=0
@17! new_p2: : v2<=0
@17! quan_var: :[]
@17! iv: :[v2]
@17! new_p1: : 3<=v2 | v2<=0
@17! new_p2: : v2<=0
@17! new_p2 (pairwisecheck): : v2<=0
infer_pure_m@17
infer_pure_m@17 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v2<=0),0)

infer_pure_m@18
infer_pure_m@18 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (16): Valid. 

<1>true&v2<=0&{FLOW,(17,18)=__norm}
inferred pure: [v2<=0]


@19! lhs_xpure_orig: x=null & n=0 | x!=null & 1<=n
@19! lhs_xpure0: 0<=n
@19! lhs_rels:None
@19! xp: true
@19! lhs(orig): : true
@19! lhs0(orig): : 0<=n
@19! rhs(orig): : @L<:v2
@19! lhs (after filter_ante): : true
@19! fml: : @L<:v2
@19! total_sub_flag:false
@19! vars overlap:[]
@19! quan_var: :[]
@19! lhs_xpure: : true
@19! lhs_xpure(w ann): : 0<=v2 & v2<=2
@19! new_p_assume: : v2<=(0-1) | 2<=v2
@19! rhs_xpure: : @L<:v2
@19! fml2: : 2<=v2
@19! new_p2: : 2<=v2
@19! quan_var: :[]
@19! iv: :[v2]
@19! new_p1: : v2<=(0-1) | 2<=v2
@19! new_p2: : 2<=v2
@19! new_p2 (pairwisecheck): : 2<=v2
infer_pure_m@19
infer_pure_m@19 EXIT out :(new es,inf pure,rel_ass) :(None,Some( 2<=v2),0)

infer_pure_m@20
infer_pure_m@20 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (17): Valid. 

<1>true&2<=v2&{FLOW,(17,18)=__norm}
inferred pure: [2<=v2]


@21! lhs_xpure_orig: a=Anon_18 & b=q & v1<:v2 & Anon_20=Anon_19 & Anon_21=r & q!=null & x!=null
@21! lhs_xpure0: a=Anon_18 & b=q & v1<:v2 & Anon_20=Anon_19 & Anon_21=r & q!=null & x!=null
@21! lhs_rels:None
@21! xp: v1<:v2
@21! lhs(orig): : v1<:v2
@21! lhs0(orig): : a=Anon_18 & b=q & v1<:v2 & Anon_20=Anon_19 & Anon_21=r & q!=null & x!=null
@21! rhs(orig): : v1<:@I
@21! lhs (after filter_ante): : v1<:v2
@21! fml: : v1<:v2 & v1<:@I
@21! total_sub_flag:false
@21! vars overlap:[]
@21! quan_var: :[v2]
@21! lhs_xpure: : v1<:v2
@21! lhs_xpure(w ann): : 0<=v2 & v2<=2 & 0<=v1 & v1<=2 & v1<:v2
@21! new_p_assume: : 3<=v1 | v1<=1
@21! rhs_xpure: : v1<:@I
@21! fml2: : v1<=1
@21! new_p2: : v1<=1
@21! quan_var: :[v2]
@21! iv: :[v1]
@21! new_p1: : 3<=v1 | v1<=1
@21! new_p2: : v1<=1
@21! new_p2 (pairwisecheck): : v1<=1
infer_pure_m@21
infer_pure_m@21 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=1),0)
Entail  (18): Valid. 

<1>true&a=Anon_18 & b=q & v1<:v2 & Anon_20=Anon_19 & Anon_21=r & v1<=1&{FLOW,(17,18)=__norm}
inferred pure: [v1<=1]


@22! lhs_xpure_orig: a=Anon_22 & b=q & Anon_24=Anon_23 & Anon_25=r & q!=null & x!=null
@22! lhs_xpure0: a=Anon_22 & b=q & Anon_24=Anon_23 & Anon_25=r & q!=null & x!=null
@22! lhs_rels:None
@22! xp: true
@22! lhs(orig): : true
@22! lhs0(orig): : a=Anon_22 & b=q & Anon_24=Anon_23 & Anon_25=r & q!=null & x!=null
@22! rhs(orig): : v1<:@I & v1<:v2
@22! lhs (after filter_ante): : true
@22! fml: : v1<:@I & v1<:v2
@22! total_sub_flag:false
@22! vars overlap:[]
@22! quan_var: :[]
@22! lhs_xpure: : true
@22! lhs_xpure(w ann): : 0<=v1 & v1<=2 & 0<=v2 & v2<=2
@22! new_p_assume: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | 0<=v1 & v1<=2 & 3<=v2 | 
v1<=1 & v1<=v2
@22! rhs_xpure: : v1<:@I & v1<:v2
@22! fml2: : v1<=1 & v1<=v2
@22! new_p2: : v1<=1 & v1<=v2
@22! quan_var: :[]
@22! iv: :[v1,v2]
@22! new_p1: : v1<=(0-1) | 3<=v1 | 0<=v1 & v1<=2 & v2<=(0-1) | 0<=v1 & v1<=2 & 3<=v2 | 
v1<=1 & v1<=v2
@22! new_p2: : v1<=1 & v1<=v2
@22! new_p2 (pairwisecheck): : v1<=1 & v1<=v2
infer_pure_m@22
infer_pure_m@22 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=1 & v1<=v2),0)
Entail  (19): Valid. 

<1>true&a=Anon_22 & b=q & Anon_24=Anon_23 & Anon_25=r & v1<=1 & v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2; v1<=1]

Entail  (20): Valid. 

<1>true&v1<:I & v1<:v2 & a=Anon_26 & b=q&{FLOW,(17,18)=__norm}


@23! lhs_xpure_orig: a=Anon_27 & b=q & x!=null
@23! lhs_xpure0: a=Anon_27 & b=q & x!=null
@23! lhs_rels:None
@23! xp: true
@23! lhs(orig): : true
@23! lhs0(orig): : a=Anon_27 & b=q & x!=null
@23! rhs(orig): : v1<:@I
@23! lhs (after filter_ante): : true
@23! fml: : v1<:@I
@23! total_sub_flag:false
@23! vars overlap:[]
@23! quan_var: :[]
@23! lhs_xpure: : true
@23! lhs_xpure(w ann): : 0<=v1 & v1<=2
@23! new_p_assume: : 3<=v1 | v1<=1
@23! rhs_xpure: : v1<:@I
@23! fml2: : v1<=1
@23! new_p2: : v1<=1
@23! quan_var: :[]
@23! iv: :[v1]
@23! new_p1: : 3<=v1 | v1<=1
@23! new_p2: : v1<=1
@23! new_p2 (pairwisecheck): : v1<=1
infer_pure_m@23
infer_pure_m@23 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v1<=1),0)
Entail  (21): Valid. 

<1>true&a=Anon_27 & b=q & v1<=1&{FLOW,(17,18)=__norm}
inferred pure: [v1<=1]

Stop Omega... 253 invocations 
