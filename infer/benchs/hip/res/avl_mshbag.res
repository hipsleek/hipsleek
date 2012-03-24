/usr/local/bin/mona

Processing file "avl_mshbag.ss"
Parsing avl_mshbag.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure get_max$int~int... 
Procedure get_max$int~int SUCCESS

Checking procedure height1$node... [add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  HEIGHT(S1,S)
!!! POST:  S=S1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [HEIGHT]
              EBase exists (Expl)(Impl)[m; n; 
                    S](ex)x::avl<m,n,S>@M[Orig][LHSCase]@ rem br[{233,234}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m_75,n_76,
                                S1: x::avl<m_75,n_76,S1>@M[Orig][LHSCase]@ rem br[{233,234}]&
                                (([HEIGHT(S1,S)][m=m_75][n=n_76 & n=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; n; 
                  S](ex)x::avl<m,n,S>@M[Orig][LHSCase]@ rem br[{233,234}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(m_1624,n_1625,
                              S1_1626: x::avl<m_1624,n_1625,S1_1626>@M[Orig][LHSCase]@ rem br[{233,234}]&
                              (
                              ([S=S1_1626][res=n & res=n_1625 & 0<=n]
                               [m=m_1624 & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S1=S) --> HEIGHT(S1,S),
 (S=S1 & S1=) --> HEIGHT(S1,S),
 (exists(p_1475:exists(p_1506:exists(q_1479:exists(q_1510:exists(n2_1512:exists(n1_1508:exists(n_76:exists(n_1473:exists(n:exists(n1_1477:exists(n2_1481:exists(m2_1511:exists(m:exists(v_int_46_1064':exists(m1_1476:exists(m2_1480:exists(m1_1507:exists(v_bool_43_1065':exists(x:exists(res:exists(m_75:exists(S1_1509:exists(S2_1513:exists(v_1505:exists(S1_1478:exists(S2_1482:exists(v_1474:(p_1475=p_1506 & 
  q_1479=q_1510 & 1+n1_1508=res & n_76=res & n_1473=res & n=res & 1+
  n1_1477=res & n2_1481=n2_1512 & S2_1513=S2_1482 & v_1505=v_1474 & 
  S1_1478=S1_1509 & 1+m1_1507+m2_1511=m_75 & m=m_75 & v_int_46_1064'=res & 
  m1_1476=m1_1507 & 1+m1_1507+m2_1480=m_75 & (1+n2_1512)<=res & 1<=res & (-2+
  res)<=n2_1512 & m_75<=-1 & v_bool_43_1065'<=0 & x!=null | p_1475=p_1506 & 
  q_1479=q_1510 & 1+n1_1508=res & n_76=res & n_1473=res & n=res & 1+
  n1_1477=res & n2_1481=n2_1512 & S2_1513=S2_1482 & v_1505=v_1474 & 
  S1_1478=S1_1509 & 1+m1_1507+m2_1511=m_75 & m=m_75 & v_int_46_1064'=res & 
  m1_1476=m1_1507 & 1+m1_1507+m2_1480=m_75 & (1+n2_1512)<=res & 1<=res & (-2+
  res)<=n2_1512 & v_bool_43_1065'<=0 & x!=null & 1<=m_75 | p_1475=p_1506 & 
  q_1479=q_1510 & 1+n2_1512=res & 2+n1_1508=res & n_76=res & n_1473=res & 
  n=res & 2+n1_1477=res & 1+n2_1481=res & S2_1513=S2_1482 & v_1505=v_1474 & 
  S1_1478=S1_1509 & 1+m1_1507+m2_1511=m_75 & m=m_75 & v_int_46_1064'=res & 
  m1_1476=m1_1507 & 1+m1_1507+m2_1480=m_75 & m_75<=-1 & v_bool_43_1065'<=0 & 
  x!=null & 1<=res | p_1475=p_1506 & q_1479=q_1510 & 1+n2_1512=res & 2+
  n1_1508=res & n_76=res & n_1473=res & n=res & 2+n1_1477=res & 1+
  n2_1481=res & S2_1513=S2_1482 & v_1505=v_1474 & S1_1478=S1_1509 & 1+
  m1_1507+m2_1511=m_75 & m=m_75 & v_int_46_1064'=res & m1_1476=m1_1507 & 1+
  m1_1507+m2_1480=m_75 & v_bool_43_1065'<=0 & x!=null & 1<=res & 1<=m_75) & 
  S1=union(S1_1509,S2_1513,{v_1505}) & S=union(S1_1478,S2_1482,{v_1474}) & 
  S!=())))))))))))))))))))))))))))) --> HEIGHT(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height1$node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

!!! REL :  ROTDL(S,Sl,Srll,Srlr,Srr,v,vrl,vr)
!!! POST:  S=union(Sl,Srll,Srlr,Srr,{v,vr,vrl})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROTDL]
              EBase exists (Expl)(Impl)[am; Sl; bm; bn; Srll; cm; cn; Srlr; 
                    dm; an; 
                    Srr](ex)EXISTS(an_51: a::avl<am,an,Sl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    b::avl<bm,bn,Srll>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    c::avl<cm,cn,Srlr>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    d::avl<dm,an_51,Srr>@M[Orig][LHSCase]@ rem br[{233,234}]&
                    (
                    ([forall(x:x <notin> Sl  | x<=v) & 
                       forall(y:y <notin> Srll  | v<=y) & 
                       forall(z:z <notin> Srll  | z<=vrl) & 
                       forall(w:w <notin> Srlr  | vrl<=w) & 
                       forall(xx:xx <notin> Srlr  | xx<=vr) & 
                       forall(yy:yy <notin> Srr  | vr<=yy) & vrl<=vr & v<=vrl]
                     [an=an_51 & an=max(bn,cn) & (-1+bn)<=cn & (-1+cn)<=bn]
                     [true][true][true][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::
                                EXISTS(flted_114_49,flted_114_50,
                                S: res::avl<flted_114_50,flted_114_49,S>@M[Orig][LHSCase]@ rem br[{233}]&
                                (
                                ([flted_114_50=3+am+bm+cm+dm]
                                 [-2+flted_114_49=an]
                                 [S!=() & ROTDL(S,Sl,Srll,Srlr,Srr,v,vrl,vr)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[am; Sl; bm; bn; Srll; cm; cn; Srlr; 
                  dm; an; 
                  Srr](ex)a::avl<am,an,Sl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  b::avl<bm,bn,Srll>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  c::avl<cm,cn,Srlr>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  d::avl<dm,an_51,Srr>@M[Orig][LHSCase]@ rem br[{233,234}]&(
                  ([(an=an_51 & bn=an_51 & an_51<=(cn+1) & cn<=an_51 & 
                     v<=vrl & vrl<=vr | an=an_51 & cn=an_51 & bn+1=an_51 & 
                     v<=vrl & vrl<=vr) & forall(x:x <notin> Sl  | x<=v) & 
                     forall(y:y <notin> Srll  | v<=y) & 
                     forall(z:z <notin> Srll  | z<=vrl) & 
                     forall(w:w <notin> Srlr  | vrl<=w) & 
                     forall(xx:xx <notin> Srlr  | xx<=vr) & 
                     forall(yy:yy <notin> Srr  | vr<=yy)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 19::
                              EXISTS(flted_114_2509,flted_114_2510,
                              S_2511: res::avl<flted_114_2510,flted_114_2509,S_2511>@M[Orig][LHSCase]@ rem br[{233}]&
                              (
                              ([S_2511!=() & S_2511=union(Sl,Srll,Srlr,Srr,
                                 {v,vr,vrl})]
                               [null!=res][-2+flted_114_2509=an & 0<=an]
                               [flted_114_2510=3+am+bm+cm+dm & 0<=am & 
                                 0<=dm & 0<=bm & 0<=cm]
                               [0<=an_51][0<=cn][0<=bn]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_1661:exists(S_1726:exists(S_1761:exists(S1_2247:exists(S2_2251:exists(v_2243:exists(S1_1842:exists(S2_1846:exists(v_1838:exists(S1_2001:exists(S2_2005:exists(v_1997:exists(S_1994:exists(S_1833:S=S1_1842 & 
  Sl=S1_1842 & S_1661=S2_1846 & Srll=S2_1846 & S_1726=S1_2001 & 
  Srlr=S1_2001 & S_1761=S2_2005 & Srr=S2_2005 & S2_2251=S_1994 & 
  S1_2247=S_1833 & v_1838=v & v_2243=vrl & v_1997=vr & v<=vrl & vrl<=vr & 
  S=union(S1_2247,S2_2251,{v_2243}) & forall(yy:yy <notin> Srr  | vr<=yy) & 
  forall(xx:xx <notin> Srlr  | xx<=vr) & forall(w:w <notin> Srlr  | 
  vrl<=w) & forall(z:z <notin> Srll  | z<=vrl) & forall(y:y <notin> Srll  | 
  v<=y) & forall(x:x <notin> Sl  | x<=v) & S_1833=union(S1_1842,S2_1846,
  {v_1838}) & S_1994=union(S1_2001,S2_2005,{v_1997}) & S_1994!=() & 
  S_1833!=()))))))))))))))) --> ROTDL(S,Sl,Srll,Srlr,Srr,v,vrl,vr)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_left$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_double_right$node~node~node~node~int~int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

!!! REL :  ROTDR(S,Sll,Slrl,Slrr,Sr,v,vl,vlr)
!!! POST:  S=union(Sll,Slrl,Slrr,Sr,{v,vl,vlr})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROTDR]
              EBase exists (Expl)(Impl)[am; Sll; bm; bn; Slrl; cm; cn; Slrr; 
                    dm; an; 
                    Sr](ex)EXISTS(an_43: a::avl<am,an,Sll>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    b::avl<bm,bn,Slrl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    c::avl<cm,cn,Slrr>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    d::avl<dm,an_43,Sr>@M[Orig][LHSCase]@ rem br[{233,234}]&(
                    ([forall(x:x <notin> Sll  | x<=vl) & 
                       forall(y:y <notin> Slrl  | vl<=y) & 
                       forall(z:z <notin> Slrl  | z<=vlr) & 
                       forall(w:w <notin> Slrr  | vlr<=w) & 
                       forall(xx:xx <notin> Slrr  | xx<=v) & 
                       forall(yy:yy <notin> Sr  | v<=yy) & vlr<=v & vl<=vlr]
                     [an=an_43 & an=max(bn,cn) & (-1+bn)<=cn & (-1+cn)<=bn]
                     [true][true][true][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                EXISTS(flted_142_41,flted_142_42,
                                S: res::avl<flted_142_42,flted_142_41,S>@M[Orig][LHSCase]@ rem br[{233}]&
                                (
                                ([flted_142_42=3+am+bm+cm+dm]
                                 [-2+flted_142_41=an]
                                 [S!=() & ROTDR(S,Sll,Slrl,Slrr,Sr,v,vl,vlr)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[am; Sll; bm; bn; Slrl; cm; cn; Slrr; 
                  dm; an; 
                  Sr](ex)a::avl<am,an,Sll>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  b::avl<bm,bn,Slrl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  c::avl<cm,cn,Slrr>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  d::avl<dm,an_43,Sr>@M[Orig][LHSCase]@ rem br[{233,234}]&(
                  ([(an=an_43 & bn=an_43 & an_43<=(cn+1) & cn<=an_43 & 
                     vl<=vlr & vlr<=v | an=an_43 & cn=an_43 & bn+1=an_43 & 
                     vl<=vlr & vlr<=v) & forall(x:x <notin> Sll  | x<=vl) & 
                     forall(y:y <notin> Slrl  | vl<=y) & 
                     forall(z:z <notin> Slrl  | z<=vlr) & 
                     forall(w:w <notin> Slrr  | vlr<=w) & 
                     forall(xx:xx <notin> Slrr  | xx<=v) & 
                     forall(yy:yy <notin> Sr  | v<=yy)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              EXISTS(flted_142_3386,flted_142_3387,
                              S_3388: res::avl<flted_142_3387,flted_142_3386,S_3388>@M[Orig][LHSCase]@ rem br[{233}]&
                              (
                              ([S_3388!=() & S_3388=union(Sll,Slrl,Slrr,Sr,
                                 {v,vl,vlr})]
                               [null!=res][-2+flted_142_3386=an & 0<=an]
                               [flted_142_3387=3+am+bm+cm+dm & 0<=am & 
                                 0<=dm & 0<=bm & 0<=cm]
                               [0<=an_43][0<=cn][0<=bn]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_2538:exists(S_2603:exists(S_2638:exists(S1_3124:exists(S2_3128:exists(v_3120:exists(S1_2719:exists(S2_2723:exists(v_2715:exists(S1_2878:exists(S2_2882:exists(v_2874:exists(S_2871:exists(S_2710:S=S1_2719 & 
  Sll=S1_2719 & S_2538=S2_2723 & Slrl=S2_2723 & S_2603=S1_2878 & 
  Slrr=S1_2878 & S_2638=S2_2882 & Sr=S2_2882 & S2_3128=S_2871 & 
  S1_3124=S_2710 & v_2715=vl & v_3120=vlr & v_2874=v & vl<=vlr & vlr<=v & 
  S=union(S1_3124,S2_3128,{v_3120}) & forall(yy:yy <notin> Sr  | v<=yy) & 
  forall(xx:xx <notin> Slrr  | xx<=v) & forall(w:w <notin> Slrr  | vlr<=w) & 
  forall(z:z <notin> Slrl  | z<=vlr) & forall(y:y <notin> Slrl  | vl<=y) & 
  forall(x:x <notin> Sll  | x<=vl) & S_2710=union(S1_2719,S2_2723,
  {v_2715}) & S_2871=union(S1_2878,S2_2882,{v_2874}) & S_2871!=() & 
  S_2710!=()))))))))))))))) --> ROTDR(S,Sll,Slrl,Slrr,Sr,v,vl,vlr)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_right$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_left$node~node~node~int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

!!! REL :  ROTL(S,Sl,Srl,Srr,v,vr)
!!! POST:  S=union(Sl,Srl,Srr,{v,vr})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROTL]
              EBase exists (Expl)(Impl)[lm; ln; Sl; rlm; rln; Srl; rrm; 
                    Srr](ex)EXISTS(flted_58_68: l::avl<lm,ln,Sl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    rl::avl<rlm,rln,Srl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    rr::avl<rrm,flted_58_68,Srr>@M[Orig][LHSCase]@ rem br[{233}]&
                    (
                    ([forall(x:x <notin> Sl  | x<=v) & forall(y:y <notin> Srl
                        | v<=y) & forall(z:z <notin> Srl  | z<=vr) & 
                       forall(w:w <notin> Srr  | vr<=w) & Srr!=() & v<=vr]
                     [(-1+rln)<=ln & ln<=rln & -1+flted_58_68=ln][true][
                     true][0!=rrm][null!=rr]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(flted_62_66,flted_62_67,
                                S: res::avl<flted_62_67,flted_62_66,S>@M[Orig][LHSCase]@ rem br[{233}]&
                                (
                                ([flted_62_67=2+lm+rlm+rrm]
                                 [-2+flted_62_66=rln]
                                 [S!=() & ROTL(S,Sl,Srl,Srr,v,vr)][null!=res]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[lm; ln; Sl; rlm; rln; Srl; rrm; 
                  Srr](ex)l::avl<lm,ln,Sl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  rl::avl<rlm,rln,Srl>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  rr::avl<rrm,flted_58_68,Srr>@M[Orig][LHSCase]@ rem br[{233}]&
                  (
                  ([(ln+1=flted_58_68 & flted_58_68<=(rln+1) & 
                     rln<=flted_58_68 & (rrm+1)<=0 & v<=vr & rr!=null | ln+
                     1=flted_58_68 & flted_58_68<=(rln+1) & 
                     rln<=flted_58_68 & v<=vr & rr!=null & 1<=rrm) & 
                     forall(x:x <notin> Sl  | x<=v) & forall(y:y <notin> Srl
                      | v<=y) & forall(z:z <notin> Srl  | z<=vr) & 
                     forall(w:w <notin> Srr  | vr<=w) & Srr!=()]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              EXISTS(flted_62_3713,flted_62_3714,
                              S_3715: res::avl<flted_62_3714,flted_62_3713,S_3715>@M[Orig][LHSCase]@ rem br[{233}]&
                              (
                              ([S_3715!=() & S_3715=union(Sl,Srl,Srr,{v,vr})]
                               [null!=res][-2+flted_62_3713=rln & 0<=rln]
                               [flted_62_3714=2+lm+rlm+rrm & 0<=lm & 
                                 0<=rrm & 0<=rlm]
                               [0<=flted_58_68][0<=ln]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m1_3491:exists(m1_3507:exists(lm:exists(flted_62_67:exists(m2_3511:exists(flted_58_3394:exists(h_71':exists(h_3488:exists(n1_3492:exists(n2_3496:exists(n1_3508:exists(n2_3512:exists(rln:exists(ln:exists(tmp2_70':exists(rl:exists(q_3510:exists(l:exists(p_3506:exists(p_3490:exists(res:exists(rrm:exists(q_3494:exists(rlm:exists(flted_62_66:exists(tmp_69':exists(v_node_70_1033':exists(m2_3495:exists(rr:exists(m:exists(n:exists(S2_3497:exists(v_3489:exists(S1_3493:exists(S1_3509:exists(S2_3513:exists(v_3505:(S2_3497=Srr & 
  S2_3513=Srl & S=Srl & S1_3509=Sl & 1+m1_3491+m2_3495=flted_62_67 & 2+m+
  m1_3507+m2_3495=flted_62_67 & 2+lm+m+m2_3495=flted_62_67 & m2_3511=m & -1+
  flted_58_3394=n & -2+h_71'=n & -1+h_3488=n & -1+n1_3492=n & -1+n2_3496=n & 
  n1_3508=n & n2_3512=n & rln=n & ln=n & tmp2_70'=v_node_70_1033' & 
  rl=q_3510 & l=p_3506 & v_3505=v & v_3489=vr & p_3490=tmp_69' & 
  res=v_node_70_1033' & rrm=m2_3495 & q_3494=rr & rlm=m & -2+flted_62_66=n & 
  v<=vr & m2_3495<=-1 & tmp_69'!=null & v_node_70_1033'!=null & rr!=null & 
  0<=m & 0<=n | S2_3497=Srr & S2_3513=Srl & S=Srl & S1_3509=Sl & 1+m1_3491+
  m2_3495=flted_62_67 & 2+m+m1_3507+m2_3495=flted_62_67 & 2+lm+m+
  m2_3495=flted_62_67 & m2_3511=m & -1+flted_58_3394=n & -2+h_71'=n & -1+
  h_3488=n & -1+n1_3492=n & -1+n2_3496=n & n1_3508=n & n2_3512=n & rln=n & 
  ln=n & tmp2_70'=v_node_70_1033' & rl=q_3510 & l=p_3506 & v_3505=v & 
  v_3489=vr & p_3490=tmp_69' & res=v_node_70_1033' & rrm=m2_3495 & 
  q_3494=rr & rlm=m & -2+flted_62_66=n & v<=vr & tmp_69'!=null & 
  v_node_70_1033'!=null & 1<=m2_3495 & rr!=null & 0<=m & 0<=n | 
  S2_3497=Srr & S2_3513=Srl & S=Srl & S1_3509=Sl & 1+m1_3491+
  m2_3495=flted_62_67 & 2+m+m1_3507+m2_3495=flted_62_67 & 2+lm+m+
  m2_3495=flted_62_67 & m2_3511=m & flted_58_3394=n & -2+h_71'=n & -1+
  h_3488=n & -1+n1_3492=n & n2_3496=n & 1+n1_3508=n & n2_3512=n & rln=n & 1+
  ln=n & tmp2_70'=v_node_70_1033' & rl=q_3510 & l=p_3506 & v_3505=v & 
  v_3489=vr & p_3490=tmp_69' & res=v_node_70_1033' & rrm=m2_3495 & 
  q_3494=rr & rlm=m & -2+flted_62_66=n & v<=vr & m2_3495<=-1 & 
  tmp_69'!=null & v_node_70_1033'!=null & rr!=null & 0<=m & 0<=n | 
  S2_3497=Srr & S2_3513=Srl & S=Srl & S1_3509=Sl & 1+m1_3491+
  m2_3495=flted_62_67 & 2+m+m1_3507+m2_3495=flted_62_67 & 2+lm+m+
  m2_3495=flted_62_67 & m2_3511=m & flted_58_3394=n & -2+h_71'=n & -1+
  h_3488=n & -1+n1_3492=n & n2_3496=n & 1+n1_3508=n & n2_3512=n & rln=n & 1+
  ln=n & tmp2_70'=v_node_70_1033' & rl=q_3510 & l=p_3506 & v_3505=v & 
  v_3489=vr & p_3490=tmp_69' & res=v_node_70_1033' & rrm=m2_3495 & 
  q_3494=rr & rlm=m & -2+flted_62_66=n & v<=vr & tmp_69'!=null & 
  v_node_70_1033'!=null & 1<=m2_3495 & rr!=null & 0<=m & 0<=n) & Srr!=() & 
  S=union(S1_3493,S2_3497,{v_3489}) & forall(w:w <notin> Srr  | vr<=w) & 
  forall(z:z <notin> Srl  | z<=vr) & forall(y:y <notin> Srl  | v<=y) & 
  forall(x:x <notin> Sl  | x<=v) & S1_3493=union(S1_3509,S2_3513,
  {v_3505}))))))))))))))))))))))))))))))))))))))) --> ROTL(S,Sl,Srl,Srr,v,vr)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_left$node~node~node~int~int SUCCESS

Checking procedure rotate_right$node~node~node~int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

!!! REL :  ROTR(S,Sll,Slr,Sr,v,vl)
!!! POST:  S=union(Sll,Slr,Sr,{v,vl})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROTR]
              EBase exists (Expl)(Impl)[llm; lln; Sll; lrm; lrn; Slr; rm; 
                    Sr](ex)EXISTS(flted_78_60: ll::avl<llm,lln,Sll>@M[Orig][LHSCase]@ rem br[{233}] * 
                    lr::avl<lrm,lrn,Slr>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                    r::avl<rm,flted_78_60,Sr>@M[Orig][LHSCase]@ rem br[{233,234}]&
                    (
                    ([forall(x:x <notin> Sll  | x<=vl) & 
                       forall(y:y <notin> Slr  | vl<=y) & 
                       forall(z:z <notin> Slr  | z<=v) & 
                       forall(w:w <notin> Sr  | v<=w) & Sll!=() & vl<=v]
                     [lrn<=lln & (-1+lln)<=lrn & 1+flted_78_60=lln][0!=llm]
                     [null!=ll][true][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(flted_82_58,flted_82_59,
                                S: res::avl<flted_82_59,flted_82_58,S>@M[Orig][LHSCase]@ rem br[{233}]&
                                (
                                ([flted_82_59=2+llm+lrm+rm]
                                 [-2+flted_82_58=lrn]
                                 [S!=() & ROTR(S,Sll,Slr,Sr,v,vl)][null!=res]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[llm; lln; Sll; lrm; lrn; Slr; rm; 
                  Sr](ex)ll::avl<llm,lln,Sll>@M[Orig][LHSCase]@ rem br[{233}] * 
                  lr::avl<lrm,lrn,Slr>@M[Orig][LHSCase]@ rem br[{233,234}] * 
                  r::avl<rm,flted_78_60,Sr>@M[Orig][LHSCase]@ rem br[{233,234}]&
                  (
                  ([(lln=1+flted_78_60 & lrn<=(flted_78_60+1) & 
                     flted_78_60<=lrn & (llm+1)<=0 & vl<=v & ll!=null | 
                     lln=1+flted_78_60 & lrn<=(flted_78_60+1) & 
                     flted_78_60<=lrn & vl<=v & ll!=null & 1<=llm) & 
                     forall(x:x <notin> Sll  | x<=vl) & 
                     forall(y:y <notin> Slr  | vl<=y) & 
                     forall(z:z <notin> Slr  | z<=v) & forall(w:w <notin> Sr
                      | v<=w) & Sll!=()]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(flted_82_4041,flted_82_4042,
                              S_4043: res::avl<flted_82_4042,flted_82_4041,S_4043>@M[Orig][LHSCase]@ rem br[{233}]&
                              (
                              ([S_4043!=() & S_4043=union(Sll,Slr,Sr,{v,vl})]
                               [null!=res][-2+flted_82_4041=lrn & 0<=lrn]
                               [flted_82_4042=2+llm+lrm+rm & 0<=llm & 
                                 0<=rm & 0<=lrm]
                               [0<=flted_78_60][0<=lln]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n2_3845:exists(n1_3841:exists(h_62':exists(h_3813:exists(n1_3817:exists(n2_3821:exists(lrn:exists(flted_78_3721:exists(lln:exists(m1_3840:exists(m2_3844:exists(llm:exists(r:exists(q_3843:exists(lr:exists(p_3839:exists(q_3819:exists(res:exists(rm:exists(flted_82_59:exists(m2_3820:exists(p_3815:exists(flted_82_58:exists(lrm:exists(tmp_61':exists(v_node_89_986':exists(m1_3816:exists(ll:exists(n:exists(m:exists(S1_3818:exists(v_3814:exists(S2_3822:exists(S1_3842:exists(S2_3846:exists(v_3838:(n2_3845=n & 
  n1_3841=n & -2+h_62'=n & -1+h_3813=n & -1+n1_3817=n & -1+n2_3821=n & 
  lrn=n & flted_78_3721=n & -1+lln=n & S2_3846=Sr & S1_3842=Slr & S=Slr & 
  S1_3818=Sll & m1_3840=m & 1+m+m2_3844=m2_3820 & llm=m1_3816 & r=q_3843 & 
  lr=p_3839 & v_3814=vl & v_3838=v & q_3819=tmp_61' & res=v_node_89_986' & 1+
  m+rm=m2_3820 & flted_82_59=1+m1_3816+m2_3820 & p_3815=ll & -2+
  flted_82_58=n & lrm=m & vl<=v & m1_3816<=-1 & tmp_61'!=null & 
  v_node_89_986'!=null & 0<=m & 0<=n & ll!=null | n2_3845=n & n1_3841=n & -2+
  h_62'=n & -1+h_3813=n & -1+n1_3817=n & -1+n2_3821=n & lrn=n & 
  flted_78_3721=n & -1+lln=n & S2_3846=Sr & S1_3842=Slr & S=Slr & 
  S1_3818=Sll & m1_3840=m & 1+m+m2_3844=m2_3820 & llm=m1_3816 & r=q_3843 & 
  lr=p_3839 & v_3814=vl & v_3838=v & q_3819=tmp_61' & res=v_node_89_986' & 1+
  m+rm=m2_3820 & flted_82_59=1+m1_3816+m2_3820 & p_3815=ll & -2+
  flted_82_58=n & lrm=m & vl<=v & tmp_61'!=null & v_node_89_986'!=null & 
  1<=m1_3816 & 0<=m & 0<=n & ll!=null | 1+n2_3845=n & n1_3841=n & -2+
  h_62'=n & -1+h_3813=n & n1_3817=n & -1+n2_3821=n & lrn=n & 1+
  flted_78_3721=n & lln=n & S2_3846=Sr & S1_3842=Slr & S=Slr & S1_3818=Sll & 
  m1_3840=m & 1+m+m2_3844=m2_3820 & llm=m1_3816 & r=q_3843 & lr=p_3839 & 
  v_3814=vl & v_3838=v & q_3819=tmp_61' & res=v_node_89_986' & 1+m+
  rm=m2_3820 & flted_82_59=1+m1_3816+m2_3820 & p_3815=ll & -2+
  flted_82_58=n & lrm=m & vl<=v & m1_3816<=-1 & tmp_61'!=null & 
  v_node_89_986'!=null & ll!=null & 0<=n & 0<=m | 1+n2_3845=n & n1_3841=n & 
  -2+h_62'=n & -1+h_3813=n & n1_3817=n & -1+n2_3821=n & lrn=n & 1+
  flted_78_3721=n & lln=n & S2_3846=Sr & S1_3842=Slr & S=Slr & S1_3818=Sll & 
  m1_3840=m & 1+m+m2_3844=m2_3820 & llm=m1_3816 & r=q_3843 & lr=p_3839 & 
  v_3814=vl & v_3838=v & q_3819=tmp_61' & res=v_node_89_986' & 1+m+
  rm=m2_3820 & flted_82_59=1+m1_3816+m2_3820 & p_3815=ll & -2+
  flted_82_58=n & lrm=m & vl<=v & tmp_61'!=null & v_node_89_986'!=null & 
  1<=m1_3816 & ll!=null & 0<=n & 0<=m) & Sll!=() & S=union(S1_3818,S2_3822,
  {v_3814}) & forall(w:w <notin> Sr  | v<=w) & forall(z:z <notin> Slr  | 
  z<=v) & forall(y:y <notin> Slr  | vl<=y) & forall(x:x <notin> Sll  | 
  x<=vl) & S2_3822=union(S1_3842,S2_3846,
  {v_3838})))))))))))))))))))))))))))))))))))))) --> ROTR(S,Sll,Slr,Sr,v,vl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_right$node~node~node~int~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 3.56 second(s)
	Time spent in main process: 1.3 second(s)
	Time spent in child processes: 2.26 second(s)
