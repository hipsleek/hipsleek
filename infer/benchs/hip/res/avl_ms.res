
Processing file "avl_ms.ss"
Parsing avl_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure build_avl1$node~node... 
!!! OLD SPECS: ((None,[]),EInfer [x,y,res]
              EBase exists (Expl)(Impl)[mx; 
                    my](ex)x::avl2<mx>@M[Orig][LHSCase]@ rem br[{649}] * 
                    y::avl2<my>@M[Orig][LHSCase]@ rem br[{650,649}]&(
                    ([null!=x][0<=mx & 0!=mx][0<=my]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(k: res::avl2<k>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[mx; 
                  my](ex)x::avl2<mx>@M[Orig][LHSCase]@ rem br[{649}] * 
                  y::avl2<my>@M[Orig][LHSCase]@ rem br[{650,649}]&(
                  ([x!=null][1<=mx][0<=my]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(k_1501: res::avl2<k_1501>@M[Orig][LHSCase]@ rem br[{650,649}]&
                              (
                              ([res!=null][x!=null]
                               [k_1501=1+mx+my & 0<=mx & 1<=mx & 0<=my]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl1$node~node SUCCESS

Checking procedure build_avl2$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [x,y,z]
              EBase exists (Expl)(Impl)[my; mz; Anon_12; Anon_13; Anon_14; 
                    Anon_15](ex)y::avl2<my>@M[Orig][LHSCase]@ rem br[{649}] * 
                    z::avl2<mz>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                    x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                    ([null!=y][0<=my & 0!=my][0<=mz][x!=null]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::ref [x]
                                EXISTS(k: x'::avl2<k>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[my; mz; Anon_12; Anon_13; Anon_14; 
                  Anon_15](ex)y::avl2<my>@M[Orig][LHSCase]@ rem br[{649}] * 
                  z::avl2<mz>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                  x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                  ([y!=null][1<=my][0<=mz][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::ref [x]
                              EXISTS(k_1583: x'::avl2<k_1583>@M[Orig][LHSCase]@ rem br[{650,649}]&
                              (
                              ([y!=null][x'=x & x'!=null]
                               [k_1583=1+my+mz & 0<=my & 1<=my & 0<=mz]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl2$node~node~node SUCCESS

Checking procedure get_max$int~int... 
Procedure get_max$int~int SUCCESS

Checking procedure height$node... 
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[m](ex)x::avl2<m>@M[Orig][LHSCase]@ rem br[{650,649}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m_87: x::avl2<m_87>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([m=m_87 & 0<=m_87]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::avl2<m>@M[Orig][LHSCase]@ rem br[{650,649}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              
                              true&(([null=x][0=res][0=m & 0<=m]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(m_1643: x::avl2<m_1643>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                 (([m=m_1643 & 1<=m & 0<=m][x!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... ERROR : non-pure heap inferred for false

Context of Verification Failure: File "avl_ms.ss",Line:77,Col:10
Last Proving Location: File "avl_ms.ss",Line:91,Col:13

ERROR: at _0_0 
Message: add_infer_pre: non-pure inferred heap : es_formula: false&(([false]))&{FLOW,(20,21)=__norm}
 es_pure: (())
 es_orig_ante: 
  Some(tmp2_79'::node<v3',h_80',c',d'>@M[Orig][]&(
  ([inf_ann_1999<=0][tmp2_79'!=null][h_1986=max(0,0) & h_80'=h_1986+1]
   [0=m_1739 & 0=dm & 0<=m_1739][m_1708=0 & m_1708=cm & 0<=m_1708]
   [m_1651=0 & m_1651=bm & 0<=m_1651][0=m & 0=am & 0<=m]
   [null=a' & null=a & null=p_1989][b'=null & b'=b & b'=q_1991]
   [c'=null & c'=c][null=d' & null=d][v1'=v1 & Anon_1987=v1'][v2'=v2][
   v3'=v3][h_1871=n_1988 & h_1712=max(0,0) & h_1871=h_1712+1]
   [null=tmp1_78' & tmp1_78'!=null]
   [0=m1_1990 & 0=m_1982 & inf_m2_2000=m2_1992 & m_1982=1+m1_1990+m2_1992 & 
     0<=m_1982 & -1<=inf_m2_2000]
   [0=res]))&
  {FLOW,(20,21)=__norm})
 es_heap: true
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [inf_ann_1999; inf_m2_2000; a; b; c; d]
 es_infer_heap: [b::avl2<inf_m2_2000>@inf_ann_1999[Orig]@ rem br[{650,649}]]
 es_infer_pure: [-1<=inf_m2_2000; inf_ann_1999<=0]
 
Procedure rotate_double_left$node~node~node~node~int~int~int FAIL-2

Exception Failure("add_infer_pre: non-pure inferred heap : es_formula: false&(([false]))&{FLOW,(20,21)=__norm}\n es_pure: (())\n es_orig_ante: \n  Some(tmp2_79'::node<v3',h_80',c',d'>@M[Orig][]&(\n  ([inf_ann_1999<=0][tmp2_79'!=null][h_1986=max(0,0) & h_80'=h_1986+1]\n   [0=m_1739 & 0=dm & 0<=m_1739][m_1708=0 & m_1708=cm & 0<=m_1708]\n   [m_1651=0 & m_1651=bm & 0<=m_1651][0=m & 0=am & 0<=m]\n   [null=a' & null=a & null=p_1989][b'=null & b'=b & b'=q_1991]\n   [c'=null & c'=c][null=d' & null=d][v1'=v1 & Anon_1987=v1'][v2'=v2][\n   v3'=v3][h_1871=n_1988 & h_1712=max(0,0) & h_1871=h_1712+1]\n   [null=tmp1_78' & tmp1_78'!=null]\n   [0=m1_1990 & 0=m_1982 & inf_m2_2000=m2_1992 & m_1982=1+m1_1990+m2_1992 & \n     0<=m_1982 & -1<=inf_m2_2000]\n   [0=res]))&\n  {FLOW,(20,21)=__norm})\n es_heap: true\n es_aux_conseq: true\n es_must_error: None\n es_var_measures: Some(MayLoop)\n es_term_err: None\n es_infer_vars: [inf_ann_1999; inf_m2_2000; a; b; c; d]\n es_infer_heap: [b::avl2<inf_m2_2000>@inf_ann_1999[Orig]@ rem br[{650,649}]]\n es_infer_pure: [-1<=inf_m2_2000; inf_ann_1999<=0]") Occurred!

Error(s) detected when checking procedure rotate_double_left$node~node~node~node~int~int~int

Checking procedure rotate_double_right$node~node~node~node~int~int~int... ERROR : non-pure heap inferred for false

Context of Verification Failure: File "avl_ms.ss",Line:101,Col:10
Last Proving Location: File "avl_ms.ss",Line:115,Col:13

ERROR: at _0_0 
Message: add_infer_pre: non-pure inferred heap : es_formula: false&(([false]))&{FLOW,(20,21)=__norm}
 es_pure: (())
 es_orig_ante: 
  Some(tmp2_76'::node<v1',h_77',c',d'>@M[Orig][]&(
  ([inf_ann_2357<=0][tmp2_76'!=null][h_2344=max(0,0) & h_77'=h_2344+1]
   [0=m_2097 & 0=dm & 0<=m_2097][m_2066=0 & m_2066=cm & 0<=m_2066]
   [m_2009=0 & m_2009=bm & 0<=m_2009][0=m & 0=am & 0<=m]
   [null=a' & null=a & null=p_2347][b'=null & b'=b & b'=q_2349]
   [c'=null & c'=c][null=d' & null=d][v1'=v1][v2'=v2][v3'=v3 & Anon_2345=v3']
   [h_2229=n_2346 & h_2070=max(0,0) & h_2229=h_2070+1]
   [null=tmp1_75' & tmp1_75'!=null]
   [0=m1_2348 & 0=m_2340 & inf_m2_2358=m2_2350 & m_2340=1+m1_2348+m2_2350 & 
     0<=m_2340 & -1<=inf_m2_2358]
   [0=res]))&
  {FLOW,(20,21)=__norm})
 es_heap: true
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: Some(MayLoop)
 es_term_err: None
 es_infer_vars: [inf_ann_2357; inf_m2_2358; a; b; c; d]
 es_infer_heap: [b::avl2<inf_m2_2358>@inf_ann_2357[Orig]@ rem br[{650,649}]]
 es_infer_pure: [-1<=inf_m2_2358; inf_ann_2357<=0]
 
Procedure rotate_double_right$node~node~node~node~int~int~int FAIL-2

Exception Failure("add_infer_pre: non-pure inferred heap : es_formula: false&(([false]))&{FLOW,(20,21)=__norm}\n es_pure: (())\n es_orig_ante: \n  Some(tmp2_76'::node<v1',h_77',c',d'>@M[Orig][]&(\n  ([inf_ann_2357<=0][tmp2_76'!=null][h_2344=max(0,0) & h_77'=h_2344+1]\n   [0=m_2097 & 0=dm & 0<=m_2097][m_2066=0 & m_2066=cm & 0<=m_2066]\n   [m_2009=0 & m_2009=bm & 0<=m_2009][0=m & 0=am & 0<=m]\n   [null=a' & null=a & null=p_2347][b'=null & b'=b & b'=q_2349]\n   [c'=null & c'=c][null=d' & null=d][v1'=v1][v2'=v2][v3'=v3 & Anon_2345=v3']\n   [h_2229=n_2346 & h_2070=max(0,0) & h_2229=h_2070+1]\n   [null=tmp1_75' & tmp1_75'!=null]\n   [0=m1_2348 & 0=m_2340 & inf_m2_2358=m2_2350 & m_2340=1+m1_2348+m2_2350 & \n     0<=m_2340 & -1<=inf_m2_2358]\n   [0=res]))&\n  {FLOW,(20,21)=__norm})\n es_heap: true\n es_aux_conseq: true\n es_must_error: None\n es_var_measures: Some(MayLoop)\n es_term_err: None\n es_infer_vars: [inf_ann_2357; inf_m2_2358; a; b; c; d]\n es_infer_heap: [b::avl2<inf_m2_2358>@inf_ann_2357[Orig]@ rem br[{650,649}]]\n es_infer_pure: [-1<=inf_m2_2358; inf_ann_2357<=0]") Occurred!

Error(s) detected when checking procedure rotate_double_right$node~node~node~node~int~int~int

Checking procedure rotate_left$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [l,rl,rr,res,k]
              EBase exists (Expl)(Impl)[lm; rlm; 
                    rrm](ex)l::avl2<lm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                    rl::avl2<rlm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                    rr::avl2<rrm>@M[Orig][LHSCase]@ rem br[{650,649}]&(
                    ([0<=lm][0<=rlm][0<=rrm]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 3::
                                res::avl2<k>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[lm; rlm; 
                  rrm](ex)l::avl2<lm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                  rl::avl2<rlm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                  rr::avl2<rrm>@M[Orig][LHSCase]@ rem br[{650,649}]&(
                  ([0<=lm][0<=rlm][0<=rrm]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 3::
                              
                              EXISTS(k_2443: res::avl2<k_2443>@M[Orig][LHSCase]@ rem br[{650,649}]&
                              (
                              ([0<=rrm][0<=k_2443][0<=rlm][res!=null][
                               null=l][0=lm & 0<=lm]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(k_2444: res::avl2<k_2444>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                 (
                                 ([2+lm+rlm+rrm=k_2444 & 0<=lm & (2+lm+
                                    rrm)<=k_2444 & 0<=rlm & 1<=lm & 0<=rrm]
                                  [l!=null][res!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_left$node~node~node SUCCESS

Checking procedure rotate_right$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [ll,lr,r,res]
              EBase exists (Expl)(Impl)[llm; lrm; 
                    rm](ex)ll::avl2<llm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                    lr::avl2<lrm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                    r::avl2<rm>@M[Orig][LHSCase]@ rem br[{650,649}]&(
                    ([0<=llm][0<=lrm][0<=rm]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 9::
                                EXISTS(k: res::avl2<k>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[llm; lrm; 
                  rm](ex)ll::avl2<llm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                  lr::avl2<lrm>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                  r::avl2<rm>@M[Orig][LHSCase]@ rem br[{650,649}]&(
                  ([0<=llm][0<=lrm][0<=rm]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 9::
                              
                              EXISTS(k_2528: res::avl2<k_2528>@M[Orig][LHSCase]@ rem br[{650,649}]&
                              (
                              ([0<=lrm][0<=k_2528][0<=llm][res!=null][
                               null=r][0=rm & 0<=rm]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(k_2529: res::avl2<k_2529>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                 (
                                 ([2+llm+lrm+rm=k_2529 & 0<=llm & (2+lrm+
                                    rm)<=k_2529 & 1<=rm & 0<=rm & 0<=lrm]
                                  [r!=null][res!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_right$node~node~node SUCCESS

Checking procedure insert$node~int... 
( [(476::,0 ); (476::,0 ); (430::,0 ); (430::,0 ); (429::,1 ); (429::,1 )]) :avl_ms.ss:175: 25: bind: node  v_node_175_992'::node<val_175_993',height_175_994',left_175_995',right_175_996'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):avl_ms.ss:175: 25:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(476::,0 ); (476::,0 ); (430::,0 ); (430::,0 ); (429::,1 ); (429::,1
          )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_171_2598=null & v_node_171_2598=v_node_175_992' |-  v_node_175_992'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

( [(436::,0 ); (436::,0 ); (430::,1 ); (430::,1 ); (429::,1 ); (429::,1 )]) :avl_ms.ss:196: 15: bind: node  v_node_196_1141'::node<val_196_1142',height_196_1143',left_196_1144',right_196_1145'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):avl_ms.ss:196: 15:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(436::,0 ); (436::,0 ); (430::,1 ); (430::,1 ); (429::,1 ); (429::,1
          )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_193_2816=null & v_node_193_2816=v_node_196_1141' |-  v_node_196_1141'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [INS,x,a]
              EBase exists (Expl)(Impl)[m](ex)x::avl2<m>@M[Orig][LHSCase]@ rem br[{650,649}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(k: res::avl2<k>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([0<=k & INS(k,m)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::avl2<m>@M[Orig][LHSCase]@ rem br[{650,649}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              EXISTS(k_3011: res::avl2<k_3011>@M[Orig][LHSCase]@ rem br[{650,649}]&
                              (([0<=k_3011 & 0<=m & INS(k_3011,m)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int result FAIL-1

Checking procedure insert_inline$node~int... 
( [(330::,0 ); (330::,0 ); (220::,0 ); (220::,0 ); (219::,1 ); (219::,1 )]) :avl_ms.ss:235: 25: bind: node  k1_60'::node<val_235_638',height_235_639',left_235_640',right_235_641'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):avl_ms.ss:235: 25:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(330::,0 ); (330::,0 ); (220::,0 ); (220::,0 ); (219::,1 ); (219::,1
          )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_231_3080=null & v_node_231_3080=k1_60' |-  k1_60'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

( [(226::,0 ); (226::,0 ); (220::,1 ); (220::,1 ); (219::,1 ); (219::,1 )]) :avl_ms.ss:289: 25: bind: node  k1_60'::node<val_289_810',height_289_811',left_289_812',right_289_813'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):avl_ms.ss:289: 25:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(226::,0 ); (226::,0 ); (220::,1 ); (220::,1 ); (219::,1 ); (219::,1
          )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_285_3310=null & v_node_285_3310=k1_60' |-  k1_60'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [x,INSL]
              EBase exists (Expl)(Impl)[m](ex)x::avl2<m>@M[Orig][LHSCase]@ rem br[{650,649}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 69::
                                EXISTS(k: res::avl2<k>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                (([0<=k & INSL(m,k)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::avl2<m>@M[Orig][LHSCase]@ rem br[{650,649}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 69::
                              EXISTS(k_3515: res::avl2<k_3515>@M[Orig][LHSCase]@ rem br[{650,649}]&
                              (([0<=k_3515 & 0<=m & INSL(m,k_3515)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert_inline$node~int result FAIL-1

Checking procedure merge$node~node... 
!!! REL :  MRG1(s2,k1)
!!! POST:  s2>=0 & s2=k1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG1,t1,t2]
              ECase case {
                     t1=null -> ((None,[]),EBase exists (Expl)(Impl)[s2](ex)
                                                 t2::avl2<s2>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                 (([0<=s2]))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 152::
                                                             EXISTS(k1: 
                                                             res::avl2<k1>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                             (
                                                             ([0<=k1 & 
                                                                MRG1(s2,k1)]
                                                              ))&
                                                             {FLOW,(20,21)=__norm}))
                     ;
                     t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; 
                                                  s2](ex)t1::avl2<s1>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                                                  t2::avl2<s2>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                  (([0<=s1][0<=s2]))&
                                                  {FLOW,(20,21)=__norm}
                                                    EBase true&MayLoop&
                                                          {FLOW,(1,23)=__flow}
                                                            EAssume 153::
                                                              EXISTS(flted_450_57: 
                                                              res::avl2<flted_450_57>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                              (
                                                              ([0<=flted_450_57 & 
                                                                 flted_450_57=s1+
                                                                 s2]
                                                               ))&
                                                              {FLOW,(20,21)=__norm}))
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   t1=null -> ((None,[]),EBase exists (Expl)(Impl)[s2](ex)
                                               t2::avl2<s2>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                               (([0<=s2]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 152::
                                                           EXISTS(k1_3641: 
                                                           res::avl2<k1_3641>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                           (
                                                           ([s2=k1_3641 & 
                                                              0<=s2]
                                                            [null=t1]))&
                                                           {FLOW,(20,21)=__norm}))
                   ;
                   t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; 
                                                s2](ex)t1::avl2<s1>@M[Orig][LHSCase]@ rem br[{650,649}] * 
                                                t2::avl2<s2>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                (([0<=s1][0<=s2]))&
                                                {FLOW,(20,21)=__norm}
                                                  EBase true&(([MayLoop]))&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 153::
                                                            EXISTS(flted_450_3642: 
                                                            res::avl2<flted_450_3642>@M[Orig][LHSCase]@ rem br[{650,649}]&
                                                            (
                                                            ([0<=flted_450_3642 & 
                                                               0<=s1 & 
                                                               flted_450_3642=s1+
                                                               s2 & 0<=s2]
                                                             [t1!=null]))&
                                                            {FLOW,(20,21)=__norm}))
                   
                   })
!!! NEW RELS:[ (s2=k1 & 0<=k1) --> MRG1(s2,k1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge$node~node SUCCESS

Termination checking result:

Stop Omega... 1414 invocations 
16 false contexts at: ( (459,17)  (459,24)  (463,3)  (463,22)  (463,10)  (462,15)  (462,27)  (462,8)  (461,14)  (461,26)  (461,8)  (461,3)  (340,12)  (280,14)  (209,14)  (188,12) )

Total verification time: 0.83 second(s)
	Time spent in main process: 0.58 second(s)
	Time spent in child processes: 0.25 second(s)
