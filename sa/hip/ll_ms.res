Starting Omega...oc
Translating global variables to procedure parameters...

!!!sa/hip/ll-size.ss:10: 9: 
 view ll<n:int>= 
  
   EBase {204}->emp&self=null & n=0&{FLOW,(1,25)=__flow}[]
  eor 
   EBase exists (Expl)(Impl)[Anon_14; 
         q](ex){203}->EXISTS(flted_11_18: self::node<Anon_14,q>@M[Orig] * 
         q::ll<flted_11_18>@M[Orig]&flted_11_18+1=n&{FLOW,(1,25)=__flow})[]
  
  inv: 0<=n
  inv_lock: None
  unstructured formula: 
   {204}->emp&self=null & n=0&{FLOW,(1,25)=__flow}[]
   || {203}->EXISTS(flted_11_18,Anon_14,q: self::node<Anon_14,q>@M[Orig] * 
      q::ll<flted_11_18>@M[Orig][LHSCase]&flted_11_18+1=n&
      {FLOW,(1,25)=__flow})[]
  xform: 0<=n
  is_recursive?: true
  view_data_name: node
  self preds: []
  materialized vars: 
  addr vars: 
  uni_vars: []
  bag of addr: 
  raw base case: {204}->emp&self=null & n=0&{FLOW,(1,25)=__flow}[]
  view_complex_inv: None
  prune branches: ,
  prune conditions: {
}
  prune baga conditions: 
  prune invs:0:,
!!!:0: 0: SAT #1
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #2
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #3
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #4
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #5
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #6
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #7
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #8
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #9
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #10
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #11
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #12
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #13
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #14
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #15
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #16
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #17
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #18
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #19
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #20
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #21
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #22
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #23
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #24
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #25
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #26
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #27
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #28
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #29
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #30
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #31
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #32
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #33
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #34
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #35
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #36
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #37
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #38
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #39
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #40
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #41
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #42
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #43
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #44
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #45
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #46
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #47
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #48
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #49
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #50
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #51
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #52
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #53
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #54
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #55
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #56
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #57
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #58
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #59
!!!:0: 0:  !((a=null | a!=null))
!!!:0: 0: SAT #60
!!!:0: 0:  a=null & a!=null
!!!:0: 0: SAT #61
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #62
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #63
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #64
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #65
!!!:0: 0:  !((a | !(a)))
!!!:0: 0: SAT #66
!!!:0: 0:  a & !(a)
!!!:0: 0: SAT #67
!!!:0: 0:  !((a | !(a)))
!!!:0: 0: SAT #68
!!!:0: 0:  a & !(a)
!!!:0: 0: SAT #69
!!!:0: 0:  !((b | !(b)))
!!!:0: 0: SAT #70
!!!:0: 0:  b & !(b)
!!!:0: 0: SAT #71
!!!:0: 0:  !((a | !(a)))
!!!:0: 0: SAT #72
!!!:0: 0:  a & !(a)
!!!:0: 0: SAT #73
!!!:0: 0:  !((b | !(b)))
!!!:0: 0: SAT #74
!!!:0: 0:  b & !(b)
!!!:0: 0: SAT #75
!!!:0: 0:  !((b<=a | a<b))
!!!:0: 0: SAT #76
!!!:0: 0:  b<=a & a<b
!!!:0: 0: SAT #77
!!!:0: 0:  !((b<a | a<=b))
!!!:0: 0: SAT #78
!!!:0: 0:  b<a & a<=b
!!!:0: 0: SAT #79
!!!:0: 0:  !((a<=b | b<a))
!!!:0: 0: SAT #80
!!!:0: 0:  a<=b & b<a
!!!:0: 0: SAT #81
!!!:0: 0:  !((a<b | b<=a))
!!!:0: 0: SAT #82
!!!:0: 0:  a<b & b<=a
!!!:0: 0: SAT #83
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #84
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #85
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #86
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #87
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #88
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #89
!!!:0: 0:  !((a=b | a!=b))
!!!:0: 0: SAT #90
!!!:0: 0:  a=b & a!=b
!!!:0: 0: SAT #91
!!!:0: 0:  !((0<=a | a<0))
!!!:0: 0: SAT #92
!!!:0: 0:  0<=a & a<0
!!!:0: 0: SAT #93
!!!:0: 0:  !((1<=b | (b+1)<=0 | 0<(b+1) & b<1))
!!!:0: 0: SAT #94
!!!:0: 0:  1<=b & (b+1)<=0
!!!:0: 0: SAT #95
!!!:0: 0:  1<=b & 0<(b+1) & b<1
!!!:0: 0: SAT #96
!!!:0: 0:  (b+1)<=0 & 0<(b+1) & b<1
!!!:0: 0: SAT #97
!!!:0: 0:  !((a<b | b<=a))
!!!:0: 0: SAT #98
!!!:0: 0:  a<b & b<=a
!!!:0: 0: SAT #99
!!!:0: 0:  !((a<(b+b) | (b+b)<=a))
!!!:0: 0: SAT #100
!!!:0: 0:  a<(b+b) & (b+b)<=a
!!!:0: 0: SAT #101
!!!:0: 0:  !((1<=b | (b+1)<=0 | 0<(b+1) & b<1))
!!!:0: 0: SAT #102
!!!:0: 0:  1<=b & (b+1)<=0
!!!:0: 0: SAT #103
!!!:0: 0:  1<=b & 0<(b+1) & b<1
!!!:0: 0: SAT #104
!!!:0: 0:  (b+1)<=0 & 0<(b+1) & b<1
!!!:0: 0: SAT #105
!!!:0: 0:  !((b=0 | b!=0))
!!!:0: 0: SAT #106
!!!:0: 0:  b=0 & b!=0
!!!:0: 0: SAT #107
!!!:0: 0:  !((b!=0 | b=0))
!!!:0: 0: SAT #108
!!!:0: 0:  b!=0 & b=0
!!!:0: 0: SAT #109
!!!:0: 0:  !((0<=a | a<0))
!!!:0: 0: SAT #110
!!!:0: 0:  0<=a & a<0
!!!:0: 0: SAT #111
!!!:0: 0:  !((1<=b | (b+1)<=0 | 0<(b+1) & b<1))
!!!:0: 0: SAT #112
!!!:0: 0:  1<=b & (b+1)<=0
!!!:0: 0: SAT #113
!!!:0: 0:  1<=b & 0<(b+1) & b<1
!!!:0: 0: SAT #114
!!!:0: 0:  (b+1)<=0 & 0<(b+1) & b<1
!!!:0: 0: SAT #115
!!!:0: 0:  !((1<=b | (b+1)<=0 | 0<(b+1) & b<1))
!!!:0: 0: SAT #116
!!!:0: 0:  1<=b & (b+1)<=0
!!!:0: 0: SAT #117
!!!:0: 0:  1<=b & 0<(b+1) & b<1
!!!:0: 0: SAT #118
!!!:0: 0:  (b+1)<=0 & 0<(b+1) & b<1gather_type_info_b_formula: relation SIZEH

!!!sa/hip/ll-size.ss:10: 9: heap_entail_one_context:
ctx:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
conseq:
 emp&0<=n&{FLOW,(1,25)=__flow}[]

!!!:0: 0: SAT #119
!!!:0: 0:  self=null & n=0 | self!=null & 1<=n
!!!sa/hip/ll-size.ss:10: 9: heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
conseq:
 emp&0<=n&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:10: 9: heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:10: 9: heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
conseq:
 emp&0<=n&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:10: 9: heap_entail_conjunct:
context:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
conseq:
 emp&0<=n&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:10: 9: heap_entail_conjunct_helper:
context:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
conseq:
 emp&0<=n&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:10: 9: heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
conseq:
 emp&0<=n&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:10: 9: heap_entail_empty_heap: ctx:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:10: 9: heap_entail_empty_heap: rhs:
 0<=n
!!!sa/hip/ll-size.ss:10: 9: rhs_p : : 0<=n
!!!sa/hip/ll-size.ss:10: 9: conseq0 : : 0<=n
!!!sa/hip/ll-size.ss:10: 9: >>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:10: 9: ante0 : : self=null & n=0 | self!=null & 1<=n
!!!sa/hip/ll-size.ss:10: 9: ante1 : : self=null & n=0 | self!=null & 1<=n
!!!sa/hip/ll-size.ss:10: 9: conseq : : 0<=n
!!!:0: 0: IMP #1
!!!:0: 0: >>>>>> imply_mix_formula: pure <<<<<<
!!!:0: 0: ante: :[ self=null & n=0, self!=null & 1<=n]
!!!:0: 0: coseq : : 0<=n
!!!:0: 0: h : : self=null & n=0
!!!:0: 0: IMP #120
!!!:0: 0: imply_timeout: ante:  self=null & n=0
!!!:0: 0: imply_timeout: conseq:  0<=n
!!!:0: 0: ante 1: : self=null & n=0
!!!:0: 0: ante 3: : self=null
!!!:0: 0: ante 4: : self=null
!!!:0: 0: res : :true
!!!:0: 0: ante: :[ self!=null & 1<=n]
!!!:0: 0: coseq : : 0<=n
!!!:0: 0: h : : self!=null & 1<=n
!!!:0: 0: IMP #121
!!!:0: 0: imply_timeout: ante:  self!=null & 1<=n
!!!:0: 0: imply_timeout: conseq:  0<=n
!!!:0: 0: ante 1: : self!=null & 1<=n
!!!:0: 0: ante 3: : self!=null & 1<=n
!!!:0: 0: ante 4: : self!=null & 1<=n
!!!:0: 0: res : :true
!!!:0: 0: ante: :[]
!!!:0: 0: coseq : : 0<=n
!!!sa/hip/ll-size.ss:10: 9: heap_entail_empty_heap: formula is valid
!!!sa/hip/ll-size.ss:10: 9: heap_entail_empty_heap: res_ctx:
 es_formula: emp&self=null & n=0 | self!=null & 1<=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
!!!:0: 0: IMP #0

!!!:0: 0: IMP #122
!!!:0: 0: imply_timeout: ante:  self=null & n=0
!!!:0: 0: imply_timeout: conseq:  self=null
!!!:0: 0: ante 1: : self=null & n=0
!!!:0: 0: ante 3: : self=null
!!!:0: 0: ante 4: : self=null
!!!:0: 0: SAT #123
!!!:0: 0:  self=null & (n=1 & self!=null | self!=null & 2<=n)
!!!:0: 0: IMP #0

!!!:0: 0: IMP #124
!!!:0: 0: imply_timeout: ante:  self=null & n=0
!!!:0: 0: imply_timeout: conseq:  n=0
!!!:0: 0: ante 1: : self=null & n=0
!!!:0: 0: ante 3: : self=null
!!!:0: 0: ante 4: : self=null
!!!:0: 0: SAT #125
!!!:0: 0:  n=0 & (n=1 & self!=null | self!=null & 2<=n)
!!!:0: 0: SAT #126
!!!:0: 0:  self=null & n=0
!!!:0: 0: SAT #127
!!!:0: 0:  exists(q:exists(flted_11_18:flted_11_18+1=n & self!=null & (q=null & 
flted_11_18=0 | q!=null & 1<=flted_11_18)))
!!!:0: 0: Mutual Grps with Phases:[]
!!!:0: 0: Mutual Grps:[]
!!!:0: 0: Phase Vars Added:[]
!!!:0: 0: f : : forall(k:i<=k & k<=j | a[k]=b[k])
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: f : : amodr(a,b,i,j)
!!!:0: 0: NONE #
!!!:0: 0: f : : i>j | i<=j & forall(k:k<i | k>j | low<=(a[k]) & (a[k])<=high)
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: f : : bnd(a,i,j,low,high)
!!!:0: 0: NONE #
!!!:0: 0: f : : dom(a,l,h)
!!!:0: 0: NONE #
!!!:0: 0: f : : dom(a,low,high) & low<=l & h<=high
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: f : : domb(a,l,h)
!!!:0: 0: NONE #
!!!:0: 0: f : : domb(a,low,high) & low<=l & h<=high
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: NONE #
!!!:0: 0: SCC:[[(dispose$node,0)],[(size_helper$node~int,1)]]
Checking procedure size_helper$node~int... 
!!!sa/hip/ll-size.ss:24: 0: Checking procedure size_helper$node~int... 
!!!sa/hip/ll-size.ss:24: 0: Specs :
 ((None,[]),EInfer [SIZEH,H,H1]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [n]
                                H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[])
!!!:0: 0: check_specs: EInfer:  es_formula: emp&x'=x & n'=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 

!!!:0: 0: check_specs: EBase:  es_formula: emp&x'=x & n'=n&{FLOW,(1,25)=__flow}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 

!!!:0: 0: check_specs: EBase:  es_formula: H(x)&x'=x & n'=n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 

!!!:0: 0: check_specs: EAssume:  es_formula: H(x)&x'=x & n'=n & MayLoop&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 

!!!:0: 0: SAT #128
!!!:0: 0:  x'=x & n'=n & MayLoop
!!!sa/hip/ll-size.ss:27: 11: heap_entail_one_context:
ctx:
 es_formula: H(x)&x'=x & n'=n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(1,25)=__flow}[]

!!!sa/hip/ll-size.ss:29: 6: 
Verification Context:(Line:27,Col:11)
Proving precondition in method is_null___$node for spec:
 ((None,[]),ECase case {
                   x'=null -> ((None,[]),EBase emp&true&
                                               {FLOW,(22,23)=__norm}[]
                                                 EBase emp&Term&
                                                       {FLOW,(1,25)=__flow}[]
                                                         EAssume 191::
                                                           emp&res & x'=null&
                                                           {FLOW,(22,23)=__norm}[])
                   ;
                   x'!=null -> ((None,[]),EBase emp&true&
                                                {FLOW,(22,23)=__norm}[]
                                                  EBase emp&Term&
                                                        {FLOW,(1,25)=__flow}[]
                                                          EAssume 192::
                                                            emp&!(res) & 
                                                            x'!=null&
                                                            {FLOW,(22,23)=__norm}[])
                   
                   })

!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_init struc_list_failesc_context_init:
tid:None
conseq: ((None,[]),ECase case {
                   x'=null -> ((None,[]),EBase emp&true&
                                               {FLOW,(22,23)=__norm}[]
                                                 EBase emp&Term&
                                                       {FLOW,(1,25)=__flow}[]
                                                         EAssume 191::
                                                           emp&res & x'=null&
                                                           {FLOW,(22,23)=__norm}[])
                   ;
                   x'!=null -> ((None,[]),EBase emp&true&
                                                {FLOW,(22,23)=__norm}[]
                                                  EBase emp&Term&
                                                        {FLOW,(1,25)=__flow}[]
                                                          EAssume 192::
                                                            emp&!(res) & 
                                                            x'!=null&
                                                            {FLOW,(22,23)=__norm}[])
                   
                   })
ctx:
 List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:H(x)&x'=x & n'=n & MayLoop&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [SIZEH]

 ]

!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_struc_failesc_context:
tid:None
ctx:
 
 Successful States:
 [
  Label: 
  State:H(x)&x'=x & n'=n & MayLoop&{FLOW,(22,23)=__norm}[]
        es_infer_vars/rel: [SIZEH]

  ]
conseq:
 ((None,[]),ECase case {
                   x'=null -> ((None,[]),EBase emp&true&
                                               {FLOW,(22,23)=__norm}[]
                                                 EBase emp&Term&
                                                       {FLOW,(1,25)=__flow}[]
                                                         EAssume 191::
                                                           emp&res & x'=null&
                                                           {FLOW,(22,23)=__norm}[])
                   ;
                   x'!=null -> ((None,[]),EBase emp&true&
                                                {FLOW,(22,23)=__norm}[]
                                                  EBase emp&Term&
                                                        {FLOW,(1,25)=__flow}[]
                                                          EAssume 192::
                                                            emp&
                                                            212::!(res) & 
                                                            x'!=null&
                                                            {FLOW,(22,23)=__norm}[])
                   
                   })
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: H(x)&x'=x & n'=n & MayLoop&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 ((None,[]),ECase case {
                   x'=null -> ((None,[]),EBase emp&true&
                                               {FLOW,(22,23)=__norm}[]
                                                 EBase emp&Term&
                                                       {FLOW,(1,25)=__flow}[]
                                                         EAssume 191::
                                                           emp&res & x'=null&
                                                           {FLOW,(22,23)=__norm}[])
                   ;
                   x'!=null -> ((None,[]),EBase emp&true&
                                                {FLOW,(22,23)=__norm}[]
                                                  EBase emp&Term&
                                                        {FLOW,(1,25)=__flow}[]
                                                          EAssume 192::
                                                            emp&
                                                            212::!(res) & 
                                                            x'!=null&
                                                            {FLOW,(22,23)=__norm}[])
                   
                   })
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: H(x)&x'=x & n'=n & MayLoop&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 ((None,[]),ECase case {
                   x'=null -> ((None,[]),EBase emp&true&
                                               {FLOW,(22,23)=__norm}[]
                                                 EBase emp&Term&
                                                       {FLOW,(1,25)=__flow}[]
                                                         EAssume 191::
                                                           emp&res & x'=null&
                                                           {FLOW,(22,23)=__norm}[])
                   ;
                   x'!=null -> ((None,[]),EBase emp&true&
                                                {FLOW,(22,23)=__norm}[]
                                                  EBase emp&Term&
                                                        {FLOW,(1,25)=__flow}[]
                                                          EAssume 192::
                                                            emp&
                                                            212::!(res) & 
                                                            x'!=null&
                                                            {FLOW,(22,23)=__norm}[])
                   
                   })
!!!:0: 0: [entail:29][post:27]SAT #129
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & MayLoop & x'=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context:
ctx:
 es_formula: H(x)&x'=x & n'=n & MayLoop & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]

!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: H(x)&x'=x & n'=n & MayLoop & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct:
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper:
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante0 : : x'=x & n'=n & x'=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante1 : : x'=x & n'=n & x'=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase emp&Term&{FLOW,(1,25)=__flow}[]
         EAssume 191::
           emp&res & x'=null&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase emp&Term&{FLOW,(1,25)=__flow}[]
         EAssume 191::
           emp&res & x'=null&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context:
ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]

!!!:0: 0: [entail:29][post:27]SAT #130
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct:
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper:
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante0 : : x'=x & n'=n & x'=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante1 : : x'=x & n'=n & x'=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EAssume 191::
   emp&res & x'=null&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: H(x)&x'=x & n'=n & x'=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EAssume 191::
   emp&res & x'=null&{FLOW,(22,23)=__norm}[]
!!!:0: 0: [entail:29][post:27]SAT #131
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'=null & res & x'=null
!!!:0: 0: [entail:29][post:27]SAT #132
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & MayLoop & x'!=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context:
ctx:
 es_formula: H(x)&x'=x & n'=n & MayLoop & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]

!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: H(x)&x'=x & n'=n & MayLoop & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct:
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper:
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante0 : : x'=x & n'=n & x'!=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante1 : : x'=x & n'=n & x'!=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase emp&Term&{FLOW,(1,25)=__flow}[]
         EAssume 192::
           emp&212::!(res) & x'!=null&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase emp&Term&{FLOW,(1,25)=__flow}[]
         EAssume 192::
           emp&212::!(res) & x'!=null&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context:
ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]

!!!:0: 0: [entail:29][post:27]SAT #133
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'!=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct:
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper:
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante0 : : x'=x & n'=n & x'!=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]ante1 : : x'=x & n'=n & x'!=null
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]conseq : : true
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EAssume 192::
   emp&212::!(res) & x'!=null&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:29: 6: [entail:29][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: H(x)&x'=x & n'=n & x'!=null&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EAssume 192::
   emp&212::!(res) & x'!=null&{FLOW,(22,23)=__norm}[]
!!!:0: 0: [entail:29][post:27]SAT #134
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'!=null & !(res) & x'!=null
!!!:0: 0: [entail:29][post:27]SAT #135
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & v_bool_29_549'
!!!:0: 0: [entail:29][post:27]SAT #136
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549'
!!!sa/hip/ll-size.ss:29: 2: [entail:29][post:27]conditional: then_delta:
 List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549'&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [SIZEH]
       es_var_measures: MayLoop

 ]
!!!:0: 0: [entail:29][post:27]SAT #137
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549')
!!!:0: 0: [entail:29][post:27]SAT #138
!!!:0: 0: [entail:29][post:27] x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & !(v_bool_29_549')
!!!sa/hip/ll-size.ss:29: 2: [entail:29][post:27]conditional: else_delta:
 List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549')&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [SIZEH]
       es_var_measures: MayLoop

 ]
!!!sa/hip/ll-size.ss:32: 8: [entail:29][post:27]
Verification Context:(Line:27,Col:11)
Proving precondition in method add___$int~int for spec:
 ((None,[]),EBase emp&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&Term&{FLOW,(1,25)=__flow}[]
                            EAssume 71::
                              emp&res=v_int_32_544'+n'&
                              {FLOW,(22,23)=__norm}[])

!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_init struc_list_failesc_context_init:
tid:None
conseq: ((None,[]),EBase emp&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&Term&{FLOW,(1,25)=__flow}[]
                            EAssume 71::
                              emp&res=v_int_32_544'+n'&
                              {FLOW,(22,23)=__norm}[])
ctx:
 List of Failesc Context: [FEC(0, 0, 1  [(131::,1 ); (131::,1 )])]

Successful States:
[
 Label: [(131::,1 ); (131::,1 )]
 State:H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [SIZEH]
       es_var_measures: MayLoop

 ]

!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_struc_failesc_context:
tid:None
ctx:
 
 Successful States:
 [
  Label: [(131::,1 ); (131::,1 )]
  State:H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
        es_infer_vars/rel: [SIZEH]
        es_var_measures: MayLoop

  ]
conseq:
 ((None,[]),EBase emp&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&Term&{FLOW,(1,25)=__flow}[]
                            EAssume 71::
                              emp&res=v_int_32_544'+n'&
                              {FLOW,(22,23)=__norm}[])
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 ((None,[]),EBase emp&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&Term&{FLOW,(1,25)=__flow}[]
                            EAssume 71::
                              emp&res=v_int_32_544'+n'&
                              {FLOW,(22,23)=__norm}[])
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 ((None,[]),EBase emp&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&Term&{FLOW,(1,25)=__flow}[]
                            EAssume 71::
                              emp&res=v_int_32_544'+n'&
                              {FLOW,(22,23)=__norm}[])
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]

!!!:0: 0: [entail:32][post:27]SAT #139
!!!:0: 0: [entail:32][post:27] x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]ante0 : : x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]ante1 : : x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]conseq : : true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase emp&Term&{FLOW,(1,25)=__flow}[]
         EAssume 71::
           emp&res=v_int_32_544'+n'&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase emp&Term&{FLOW,(1,25)=__flow}[]
         EAssume 71::
           emp&res=v_int_32_544'+n'&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]

!!!:0: 0: [entail:32][post:27]SAT #140
!!!:0: 0: [entail:32][post:27] x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 emp&Term&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]ante0 : : x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]ante1 : : x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]conseq : : true
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EAssume 71::
   emp&res=v_int_32_544'+n'&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:32: 8: [entail:32][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & v_int_32_544'=1&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EAssume 71::
   emp&res=v_int_32_544'+n'&{FLOW,(22,23)=__norm}[]
!!!:0: 0: [entail:32][post:27]SAT #141
!!!:0: 0: [entail:32][post:27] x'=x & n'=n & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
v_int_32_544'=1 & res=v_int_32_544'+n'
!!!sa/hip/ll-size.ss:33: 23: [entail:32][post:27]bind: unfolded context:
 List of Failesc Context: [FEC(0, 0, 1  [(131::,1 ); (131::,1 )])]

Successful States:
[
 Label: [(131::,1 ); (131::,1 )]
 State:H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [SIZEH]
       es_var_measures: MayLoop

 ]

!!!sa/hip/ll-size.ss:33: 23: [entail:32][post:27]Proving binding in method size_helper$node~int for spec  EAssume 67::ref [n]
   H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[], Line 27

!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_init struc_list_failesc_context_init:
tid:None
conseq: EBase x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
ctx:
 List of Failesc Context: [FEC(0, 0, 1  [(131::,1 ); (131::,1 )])]

Successful States:
[
 Label: [(131::,1 ); (131::,1 )]
 State:H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [SIZEH]
       es_var_measures: MayLoop

 ]

!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_struc_failesc_context:
tid:None
ctx:
 
 Successful States:
 [
  Label: [(131::,1 ); (131::,1 )]
  State:H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm}[]
        es_infer_vars/rel: [SIZEH]
        es_var_measures: MayLoop

  ]
conseq:
 EBase x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 EBase x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]

!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_split_lhs_phases: 
ante:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct:
context:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper: conseq has an non-empty heap component
context:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_non_empty_rhs_heap:
context:
 es_formula: 
  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  n'=1+n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]process_action :
 ### action =  InferHeap: ( x'::node<val_33_545',next_33_546'>@L[Orig], emp)
 ### estate =  H(x)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm}[]
  es_infer_vars_rel: [SIZEH]
  es_var_measures: MayLoop
 ### conseq =  x'::node<val_33_545',next_33_546'>@L[Orig]&true&{FLOW,(1,25)=__flow}[]


!!! es_infer_vars_hp_rel: [H,H1]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct:
context:
 es_formula: 
  HP_577(next_33_546',x) * x'::node<val_33_545',next_33_546'>@M[Orig]&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  HP_577(next_33_546',x) * x'::node<val_33_545',next_33_546'>@M[Orig]&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  HP_577(next_33_546',x) * x'::node<val_33_545',next_33_546'>@M[Orig]&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  HP_577(next_33_546',x) * x'::node<val_33_545',next_33_546'>@M[Orig]&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]ante0 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]ante1 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]conseq : : true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: formula is valid
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: res_ctx:
 es_formula: 
  HP_577(next_33_546',x) * x'::node<val_33_545',next_33_546'>@M[Orig]&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]>>>>>>> Termination Checking: size_helper$node~int <<<<<<<
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]
Verification Context:(Line:27,Col:11)
Proving precondition in method size_helper$node~int for spec:
 EBase H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
         EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                 EAssume 67::ref [n]
                   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]

!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_init struc_list_failesc_context_init:
tid:None
conseq: EBase H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
         EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                 EAssume 67::ref [n]
                   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
ctx:
 List of Failesc Context: [FEC(0, 0, 1  [(131::,1 ); (131::,1 )])]

Successful States:
[
 Label: [(131::,1 ); (131::,1 )]
 State:EXISTS(val_33_579: HP_577(v_node_33_547',x) * x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [SIZEH]
       es_var_measures: MayLoop

 ]

!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_struc_failesc_context:
tid:None
ctx:
 
 Successful States:
 [
  Label: [(131::,1 ); (131::,1 )]
  State:EXISTS(val_33_579: HP_577(v_node_33_547',x) * x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm})[]
        es_infer_vars/rel: [SIZEH]
        es_var_measures: MayLoop

  ]
conseq:
 EBase H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
         EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                 EAssume 67::ref [n]
                   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  EXISTS(val_33_579: HP_577(v_node_33_547',x) * 
  x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 EBase H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
         EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                 EAssume 67::ref [n]
                   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  EXISTS(val_33_579: HP_577(v_node_33_547',x) * 
  x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 EBase H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
         EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                 EAssume 67::ref [n]
                   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  EXISTS(val_33_579: HP_577(v_node_33_547',x) * 
  x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]

!!!:0: 0: [entail:33][post:27]SAT #142
!!!:0: 0: [entail:33][post:27] x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  EXISTS(val_33_579: HP_577(v_node_33_547',x) * 
  x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  EXISTS(val_33_579: HP_577(v_node_33_547',x) * 
  x'::node<val_33_579,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&
  x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
  n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_split_lhs_phases: 
ante:
 es_formula: 
  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&
  x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
  n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct:
context:
 es_formula: 
  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&
  x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
  n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&
  x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
  n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper: conseq has an non-empty heap component
context:
 es_formula: 
  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&
  x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
  n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_non_empty_rhs_heap:
context:
 es_formula: 
  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&
  x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
  n&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[])]
 es_var_zero_perm: 
conseq:
 H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]process_action :
 ### action =  InferHeap: ( H(v_node_33_547'), emp)
 ### estate =  HP_577(v_node_33_547',x) * x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&{FLOW,(22,23)=__norm}[]
  es_infer_vars_rel: [SIZEH]
  es_var_measures: MayLoop
 ### conseq =  H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]


!!! es_infer_vars_hp_rel: [H,H1,HP_577]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]ante0 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]ante1 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]conseq : : true
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:33: 23: [entail:33][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
         EAssume 67::ref [n]
           H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
         EAssume 67::ref [n]
           H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&MayLoop&{FLOW,(1,25)=__flow}[]

!!!:0: 0: [entail:33][post:27]SAT #143
!!!:0: 0: [entail:33][post:27] x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&MayLoop&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&MayLoop&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_conjunct:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&MayLoop&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&MayLoop&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&MayLoop&{FLOW,(1,25)=__flow}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]no relation in rhs
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]ante0 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]ante1 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+
n & x'!=null
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]conseq : : true
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_empty_heap: folding: formula is valid
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_empty_heap: folding: res_ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_one_context_struc:
ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 EAssume 67::ref [n]
   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 11: [entail:33][post:27]heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc
tid:None
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_547'>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & n'=1+n&
  {FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 EAssume 67::ref [n]
   H1(v_node_33_547')&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!:0: 0: [entail:33][post:27]SAT #144
!!!:0: 0: [entail:33][post:27] x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
n_587=1+n & SIZEH(res,n_587) & x'!=null
!!!sa/hip/ll-size.ss:27: 11: [entail:33][post:27]Pre Vars :[H,x,n]
!!!sa/hip/ll-size.ss:27: 11: [entail:33][post:27]Post Vars :[n',H1,x]
!!!sa/hip/ll-size.ss:27: 11: [entail:33][post:27]Extra Implicit Vars :[]
!!!sa/hip/ll-size.ss:27: 11: [entail:33][post:27]Extra Explicit Vars :[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_init list_partial_context_init:
tid:None
conseq: H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
ctx:
 List of Partial Context: [PC(0, 2)]
Failed States:

Successful States:
[
 Label: [(131::,0 ); (131::,0 )]
 State:es_formula: 
        H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & 
        v_bool_29_549' & v_int_30_543'=n' & res=v_int_30_543'&
        {FLOW,(22,23)=__norm}[]
       es_pure: true
       es_orig_ante: None
       es_heap: emp
       es_aux_conseq: true
       es_must_error: None
       es_var_measures: Some(MayLoop)
       es_term_err: None
       es_infer_vars_rel: [SIZEH]
       es_infer_vars_hp_rel: [H; H1]
       es_var_zero_perm: ;
 Label: [(131::,1 ); (131::,1 )]
 State:es_formula: 
        EXISTS(v_node_33_589: x'::node<val_33_586,v_node_33_589>@M[Orig] * 
        H1(v_node_33_589)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & 
        !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&
        {FLOW,(22,23)=__norm})[]
       es_pure: true
       es_orig_ante: None
       es_heap: emp
       es_aux_conseq: true
       es_must_error: None
       es_var_measures: Some(MayLoop)
       es_term_err: None
       es_infer_vars_rel: [SIZEH]
       es_infer_vars_hp_rel: [H; H1; HP_577]
       es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                        (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
       es_var_zero_perm: 
 ]

!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_struc_list_partial_context:
tid:None
ctx:
 List of Partial Context: [PC(0, 2)]
Failed States:

Successful States:
[
 Label: [(131::,0 ); (131::,0 )]
 State:es_formula: 
        H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & 
        v_bool_29_549' & v_int_30_543'=n' & res=v_int_30_543'&
        {FLOW,(22,23)=__norm}[]
       es_pure: true
       es_orig_ante: None
       es_heap: emp
       es_aux_conseq: true
       es_must_error: None
       es_var_measures: Some(MayLoop)
       es_term_err: None
       es_infer_vars_rel: [SIZEH]
       es_infer_vars_hp_rel: [H; H1]
       es_var_zero_perm: ;
 Label: [(131::,1 ); (131::,1 )]
 State:es_formula: 
        EXISTS(v_node_33_589: x'::node<val_33_586,v_node_33_589>@M[Orig] * 
        H1(v_node_33_589)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & 
        !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&
        {FLOW,(22,23)=__norm})[]
       es_pure: true
       es_orig_ante: None
       es_heap: emp
       es_aux_conseq: true
       es_must_error: None
       es_var_measures: Some(MayLoop)
       es_term_err: None
       es_infer_vars_rel: [SIZEH]
       es_infer_vars_hp_rel: [H; H1; HP_577]
       es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                        (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
       es_var_zero_perm: 
 ]
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_struc_partial_context:
tid:None
ctx:
 Failed States:
 
 Successful States:
 [
  Label: [(131::,0 ); (131::,0 )]
  State:es_formula: 
         H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & 
         v_bool_29_549' & v_int_30_543'=n' & res=v_int_30_543'&
         {FLOW,(22,23)=__norm}[]
        es_pure: true
        es_orig_ante: None
        es_heap: emp
        es_aux_conseq: true
        es_must_error: None
        es_var_measures: Some(MayLoop)
        es_term_err: None
        es_infer_vars_rel: [SIZEH]
        es_infer_vars_hp_rel: [H; H1]
        es_var_zero_perm: ;
  Label: [(131::,1 ); (131::,1 )]
  State:es_formula: 
         EXISTS(v_node_33_589: x'::node<val_33_586,v_node_33_589>@M[Orig] * 
         H1(v_node_33_589)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & 
         !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&
         {FLOW,(22,23)=__norm})[]
        es_pure: true
        es_orig_ante: None
        es_heap: emp
        es_aux_conseq: true
        es_must_error: None
        es_var_measures: Some(MayLoop)
        es_term_err: None
        es_infer_vars_rel: [SIZEH]
        es_infer_vars_hp_rel: [H; H1; HP_577]
        es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                         (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
        es_var_zero_perm: 
  ]
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]

!!!:0: 0: [entail:27][post:27]SAT #145
!!!:0: 0: [entail:27][post:27] x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
v_int_30_543'=n' & res=v_int_30_543'
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_split_lhs_phases: 
ante:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_helper: conseq has an non-empty heap component
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_non_empty_rhs_heap:
context:
 es_formula: 
  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]process_action :
 ### action =  InferHeap: ( H1(x), emp)
 ### estate =  H(x)&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
  es_infer_vars_rel: [SIZEH]
  es_var_measures: MayLoop
 ### conseq =  H1(x)&true&{FLOW,(22,23)=__norm}[]


!!! es_infer_vars_hp_rel: [H,H1]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct:
context:
 es_formula: 
  htrue&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_infer_hp_rel: [(RELASS [H,H1], H(x)&x=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  htrue&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_infer_hp_rel: [(RELASS [H,H1], H(x)&x=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  htrue&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_infer_hp_rel: [(RELASS [H,H1], H(x)&x=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!:0: 0: [entail:27][post:27]SAT #146
!!!:0: 0: [entail:27][post:27] x'=x & n'=n & res=n & v_int_30_543'=n & x=null & v_bool_29_549'
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]diff_vs:[n',v_int_30_543']
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]new_lhs (b4 elim_exists): exists(v_int_30_543':exists(n':n'=n & res=n & v_int_30_543'=n))
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]Infer Rel Ids:[SIZEH]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]LHS pure: x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
v_int_30_543'=n' & res=v_int_30_543'
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]RHS pure: SIZEH(res,n)
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]RHS Rel List:[ SIZEH(res,n)]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  htrue&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_infer_hp_rel: [(RELASS [H,H1], H(x)&x=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_infer_rel: [RELDEFN SIZEH: ( n=res) -->  SIZEH(res,n)]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]ante0 : : x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
v_int_30_543'=n' & res=v_int_30_543'
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]ante1 : : x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
v_int_30_543'=n' & res=v_int_30_543'
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]conseq : : true
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_empty_heap: formula is valid
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_empty_heap: res_ctx:
 es_formula: 
  htrue&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & v_bool_29_549' & 
  v_int_30_543'=n' & res=v_int_30_543'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1]
 es_infer_hp_rel: [(RELASS [H,H1], H(x)&x=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_infer_rel: [RELDEFN SIZEH: ( n=res) -->  SIZEH(res,n)]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_one_context:
ctx:
 es_formula: 
  EXISTS(v_node_33_589: x'::node<val_33_586,v_node_33_589>@M[Orig] * 
  H1(v_node_33_589)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]

!!!:0: 0: [entail:27][post:27]SAT #147
!!!:0: 0: [entail:27][post:27] x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
SIZEH(v_int_33_548',1+n) & res=v_int_33_548' & x'!=null
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_after_sat: invoking heap_entail_conjunct_lhs
context:
 es_formula: 
  EXISTS(v_node_33_589: x'::node<val_33_586,v_node_33_589>@M[Orig] * 
  H1(v_node_33_589)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases
!!!sa/hip/ll-size.ss:27: 11: [entail:27][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  EXISTS(v_node_33_589: x'::node<val_33_586,v_node_33_589>@M[Orig] * 
  H1(v_node_33_589)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & 
  !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&
  {FLOW,(22,23)=__norm})[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_split_rhs_phases: 
                            
ante:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_split_lhs_phases: 
ante:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct_helper: conseq has an non-empty heap component
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct_non_empty_rhs_heap:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & 
  x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
  SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 H1(x)&true&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]process_action :
 ### action =  InferHeap: ( H1(x), emp)
 ### estate =  x'::node<val_33_586,v_node_33_591>@M[Orig] * H1(v_node_33_591)&x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
  es_infer_vars_rel: [SIZEH]
  es_var_measures: MayLoop
 ### conseq =  H1(x)&true&{FLOW,(22,23)=__norm}[]


!!! es_infer_vars_hp_rel: [H,H1,HP_577]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & SIZEH(v_int_33_548',1+
  n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]); 
                  (RELASS [H1], x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct_helper:
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & SIZEH(v_int_33_548',1+
  n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]); 
                  (RELASS [H1], x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_conjunct_helper: conseq has an empty heap component
context:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & SIZEH(v_int_33_548',1+
  n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]); 
                  (RELASS [H1], x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_var_zero_perm: 
conseq:
 emp&SIZEH(res,n)&{FLOW,(22,23)=__norm}[]
!!!:0: 0: [entail:27][post:27]SAT #148
!!!:0: 0: [entail:27][post:27] x'=x & v_int_33_548'=res & !(v_bool_29_549') & x!=null & 
SIZEH(v_int_33_548',1+n)
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]diff_vs:[]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]new_lhs (b4 elim_exists): v_int_33_548'=res & SIZEH(v_int_33_548',1+n)
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]>>>>>> infer_collect_rel <<<<<<
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]Infer Rel Ids:[SIZEH]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]LHS pure: x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
SIZEH(v_int_33_548',1+n) & res=v_int_33_548'
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]RHS pure: SIZEH(res,n)
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]RHS Rel List:[ SIZEH(res,n)]
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_empty_heap: ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & SIZEH(v_int_33_548',1+
  n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]); 
                  (RELASS [H1], x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_infer_rel: [RELDEFN SIZEH: ( res=v_int_33_548' & SIZEH(v_int_33_548',1+n)) -->  SIZEH(res,n)]
 es_var_zero_perm: 
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_empty_heap: rhs:
 true
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]rhs_p : : true
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]conseq0 : : true
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]>>>>>> entail_empty_heap: cp1 <<<<<<
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]ante0 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
SIZEH(v_int_33_548',1+n) & res=v_int_33_548' & x'!=null
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]ante1 : : x'=x & x'!=null & !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
SIZEH(v_int_33_548',1+n) & res=v_int_33_548' & x'!=null
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]conseq : : true
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_empty_heap: formula is valid
!!!sa/hip/ll-size.ss:33: 4: [entail:27][post:27]heap_entail_empty_heap: res_ctx:
 es_formula: 
  x'::node<val_33_586,v_node_33_591>@M[Orig]&x'=x & x'!=null & 
  !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & SIZEH(v_int_33_548',1+
  n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars_rel: [SIZEH]
 es_infer_vars_hp_rel: [H; H1; HP_577]
 es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                  (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]); 
                  (RELASS [H1], x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
 es_infer_rel: [RELDEFN SIZEH: ( res=v_int_33_548' & SIZEH(v_int_33_548',1+n)) -->  SIZEH(res,n)]
 es_var_zero_perm: 
!!!:0: 0: [entail:27][post:27]TMP CTX:  List of Partial Context: [PC(0, 2)]
Failed States:

Successful States:
[
 Label: [(131::,0 ); (131::,0 )]
 State:es_formula: 
        htrue&x'=x & n'=n & x'=null & v_bool_29_549' & x'=null & 
        v_bool_29_549' & v_int_30_543'=n' & res=v_int_30_543'&
        {FLOW,(22,23)=__norm}[]
       es_pure: true
       es_orig_ante: None
       es_heap: emp
       es_aux_conseq: true
       es_must_error: None
       es_var_measures: Some(MayLoop)
       es_term_err: None
       es_infer_vars_rel: [SIZEH]
       es_infer_vars_hp_rel: [H; H1]
       es_infer_hp_rel: [(RELASS [H,H1], H(x)&x=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
       es_infer_rel: [RELDEFN SIZEH: ( n=res) -->  SIZEH(res,n)]
       es_var_zero_perm: ;
 Label: [(131::,1 ); (131::,1 )]
 State:es_formula: 
        x'::node<val_33_586,v_node_33_591>@M[Orig]&x'=x & x'!=null & 
        !(v_bool_29_549') & x'!=null & !(v_bool_29_549') & 
        SIZEH(v_int_33_548',1+n) & res=v_int_33_548'&{FLOW,(22,23)=__norm}[]
       es_pure: true
       es_orig_ante: None
       es_heap: emp
       es_aux_conseq: true
       es_must_error: None
       es_var_measures: Some(MayLoop)
       es_term_err: None
       es_infer_vars_rel: [SIZEH]
       es_infer_vars_hp_rel: [H; H1; HP_577]
       es_infer_hp_rel: [(RELASS [H,HP_577], H(x)&x!=null&{FLOW,(22,23)=__norm}[], x::node<val_33_545',next_33_546'>@L[Orig] * HP_577(next_33_546',x)&true&
{FLOW,(1,25)=__flow}[]); 
                        (RELASS [HP_577,H], HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
x!=null&{FLOW,(22,23)=__norm}[], H(v_node_33_547')&true&{FLOW,(22,23)=__norm}[]); 
                        (RELASS [H1], x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]
       es_infer_rel: [RELDEFN SIZEH: ( res=v_int_33_548' & SIZEH(v_int_33_548',1+n)) -->  SIZEH(res,n)]
       es_var_zero_perm: 
 ]

!!!:0: 0: [entail:27][post:27]
Proving done... Result: true

!!!sa/hip/ll-size.ss:26: 2: [entail:27][post:27]
Proving done... Result: true

!!!:0: 0: [entail:27][post:27]
INF-POST-FLAG: true
!!!:0: 0: [entail:27][post:27]>>>>>> compute_fixpoint <<<<<<
!!!:0: 0: [entail:27][post:27]Input of fixcalc: SIZEH:={[n] -> [res] -> []: (n=res ||  (exists (fc_n_593: (exists (PRIv_int_33_548:((PRIv_int_33_548=res && SIZEH(fc_n_593,PRIv_int_33_548)) && fc_n_593=1+n))) )) )
};bottomupgen([SIZEH]);
!!!:0: 0: [entail:27][post:27]Result of fixcalc: res >= n


!!!:0: 0: [entail:27][post:27]Result of fixcalc (parsed): :[ res>=n]
!!!:0: 0: [entail:27][post:27]SAT #149
!!!:0: 0: [entail:27][post:27] MayLoop
!!! OLD SPECS: ((None,[]),EInfer [SIZEH,H,H1]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [n]
                                H1(x)&SIZEH(res,n)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 67::ref [n]
                              EXISTS(H1: H1(x)&res>=n&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (n=res) --> SIZEH(res,n),
 (res=v_int_33_548' & SIZEH(v_int_33_548',1+n)) --> SIZEH(res,n)]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&x=null&{FLOW,(22,23)=__norm}[]) --> H1(x)&true&{FLOW,(22,23)=__norm}[],
 (H(x)&x!=null&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_33_545',next_33_546'>@L[Orig] * 
  HP_577(next_33_546',x)&true&{FLOW,(1,25)=__flow}[],
 (HP_577(v_node_33_547',x) * x::node<val_33_586,v_node_33_547'>@M[Orig]&
  x!=null&{FLOW,(22,23)=__norm}[]) --> H(v_node_33_547')&true&
  {FLOW,(22,23)=__norm}[],
 (x::node<val_33_586,v_node_33_591>@M[Orig]&x!=null&
  {FLOW,(22,23)=__norm}[]) --> H1(x)&true&{FLOW,(22,23)=__norm}[]]
Procedure size_helper$node~int SUCCESS

Termination checking result:

Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.33 second(s)
	Time spent in main process: 0.29 second(s)
	Time spent in child processes: 0.04 second(s)
