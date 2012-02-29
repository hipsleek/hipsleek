/usr/local/bin/mona

Processing file "dll_msb.ss"
Parsing dll_msb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure append2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP2(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                    ([0!=m][null!=x][S1!=()][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(q_215,t,
                                S: x::dll<q_215,t,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([t=m+n][APP2(S,S1,S2)][q=q_215]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(q_2042,t_2043,
                              S_2044: x::dll<q_2042,t_2043,S_2044>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S_2044=union(S1,S2)][q=q_2042]
                               [t_2043=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1934:exists(v_1779:exists(v_1932:exists(S1_1781:S1!=() & S2= & 
  S=union(S1_1934,{v_1932}) & S1=union(S1_1781,{v_1779}) & S1_1934=S2 & 
  v_1779=v_1932 & S1_1781=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1778:exists(m:exists(p_1776:exists(q_215:exists(q:exists(self_1839:exists(p_1838:exists(p:exists(v_1892:exists(S1_1894:exists(n:exists(q_1842:exists(q_1893:exists(q_1879:exists(x:exists(flted_12_1840:exists(q_1780:exists(y:exists(self_1777:exists(v_bool_184_1409':exists(v_bool_182_1414':exists(t:exists(S1_1880:exists(v_1878:exists(S1_1781:exists(v_1779:exists(S1_1843:exists(v_1841:S1_1880=union(S1_1894,
  {v_1892}) & S1_1781= & (flted_12_1778=0 & m=1 & p_1776=q & q_215=q & 
  self_1839=y & p_1838=p & v_1878=v_1779 & v_1892=v_1841 & S1_1843=S1_1894 & 
  1+n=t & q_1842=q_1893 & q_1879=y & x=self_1777 & 2+flted_12_1840=t & 
  q_1780=null & t<=0 & y!=null & self_1777!=null & 1<=v_bool_184_1409' & 
  1<=v_bool_182_1414' | flted_12_1778=0 & m=1 & p_1776=q & q_215=q & 
  self_1839=y & p_1838=p & v_1878=v_1779 & v_1892=v_1841 & S1_1843=S1_1894 & 
  1+n=t & q_1842=q_1893 & q_1879=y & x=self_1777 & 2+flted_12_1840=t & 
  q_1780=null & y!=null & self_1777!=null & 1<=v_bool_184_1409' & 
  1<=v_bool_182_1414' & 2<=t) & S2!=() & S=union(S1_1880,{v_1878}) & 
  S1=union(S1_1781,{v_1779}) & S2=union(S1_1843,{v_1841}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1781:exists(v_1779:exists(S1_1934:exists(v_1932:S1_1781= & 
  v_1779=v_1932 & S2=S1_1934 & S1=union(S1_1781,{v_1779}) & S=union(S1_1934,
  {v_1932}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1964:exists(v_1962:exists(S1_1781:exists(v_1779:S_1961!=() & 
  S1_1781!=() & S1_1781=S1_1852 & v_1779=v_1962 & S_1961=S1_1964 & 
  S2_1855=S2 & APP2(S_1961,S1_1852,S2_1855) & S1!=() & S=union(S1_1964,
  {v_1962}) & S1=union(S1_1781,{v_1779})))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... Timeout when checking #simplify  Restarting Omega after ... 23 invocations Stop Omega... 23 invocations Starting Omega...oc

!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_34; m; 
                    S3](ex)x::dll<Anon_34,m,S3>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_224,Anon_35,
                                S4: x'::dll<Anon_35,n_224,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([n=n_224]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_34; m; 
                  S3](ex)x::dll<Anon_34,m,S3>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              EXISTS(n_2286,S4_2287: true&(
                              ([S4_2287=][null=x'][0=n_2286][0=n][0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(S_2288: x'::dll<Anon_35,n_224,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                 (
                                 ([S4=S_2288 & 
                                    662::forall(_x:_x <notin> S_2288  | 
                                    _x=v) & S_2288!=()]
                                  [x'!=null][n_224=n & 1<=n_224]
                                  [Anon_2275_2282_2283=Anon_35][0<=m]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::
                                EXISTS(p_195,m,
                                S1: x::dll<p_195,m,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([DEL(S,S1)][p=p_195][true]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 53::
                              EXISTS(p_2727,m_2728,
                              S1_2729: x::dll<p_2727,m_2728,S1_2729>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (([p=p_2727][S1_2729<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2589:exists(v_2587:exists(S1_2462:exists(v_2460:exists(S1_2380:exists(v_2378:exists(S1_2575:exists(v_2573:exists(S1_2335:exists(v_2333:S1_2462=S1_2589 & 
  v_2587=v_2460 & S1_2575=union(S1_2589,{v_2587}) & S1_2380!=() & 
  S1_2335!=() & S1_2380=union(S1_2462,{v_2460}) & S1_2335=union(S1_2380,
  {v_2378}) & v_2333=v_2573 & S!=() & S1=union(S1_2575,{v_2573}) & 
  S=union(S1_2335,{v_2333})))))))))))) --> DEL(S,S1),
 (exists(S1_2380:exists(v_2378:exists(S1_2638:exists(v_2636:exists(S1_2335:exists(v_2333:S1_2380= & 
  S1_2335!=() & S1_2335=union(S1_2380,{v_2378}) & S1_2638= & v_2636=v_2333 & 
  S1=union(S1_2638,{v_2636}) & S!=() & S=union(S1_2335,
  {v_2333})))))))) --> DEL(S,S1),
 (exists(m:exists(flted_12_2522:exists(n:exists(a:exists(q_2524:exists(p_2520:exists(p:exists(p_195:exists(x:exists(p_2538:exists(v_int_295_2661:exists(n_2539:exists(tmp_197':exists(v_bool_283_1223':exists(self_2521:exists(m_2659:exists(q_2663:exists(S1_2525:exists(v_2523:exists(S1_2664:exists(v_2662:S1_2525!=() & 
  S1_2660!=() & (-1+m=m_2659 & flted_12_2522=n_2539 & -1+n=n_2539 & -1+
  a=v_int_295_2661 & q_2524=q_2663 & S1_2660=S1_2664 & S1_2525=S_2540 & 
  v_2662=v_2523 & p_2520=p_195 & p=p_195 & x=self_2521 & p_2538=self_2521 & 
  1<=v_int_295_2661 & (1+v_int_295_2661)<=n_2539 & m_2659<=-1 & 
  tmp_197'=null & !(v_bool_283_1223') & self_2521!=null & q_2663!=null & 
  DEL(S_2540,S1_2660) | -1+m=m_2659 & flted_12_2522=n_2539 & -1+n=n_2539 & 
  -1+a=v_int_295_2661 & q_2524=q_2663 & S1_2660=S1_2664 & S1_2525=S_2540 & 
  v_2662=v_2523 & p_2520=p_195 & p=p_195 & x=self_2521 & p_2538=self_2521 & 
  1<=v_int_295_2661 & (1+v_int_295_2661)<=n_2539 & tmp_197'=null & 
  !(v_bool_283_1223') & self_2521!=null & 1<=m_2659 & q_2663!=null & 
  DEL(S_2540,S1_2660)) & S!=() & S=union(S1_2525,{v_2523}) & 
  S1=union(S1_2664,{v_2662}))))))))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FGE(S,m)
!!! POST:  m <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[Anon_75; n; 
                    S](ex)x::dll<Anon_75,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 127::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_76,Anon_77,
                                   m: res::node<m,Anon_76,Anon_77>@M[Orig][]&
                                   (([FGE(S,m) & (1+v)<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_75; n; 
                  S](ex)x::dll<Anon_75,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 127::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_3282,Anon_3283,
                                 m_3284: res::node<m_3284,Anon_3282,Anon_3283>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_3284 & m_3284 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_3189:exists(Anon_75:exists(Anon_76:exists(Anon_77:exists(q_3193:exists(self_3190:exists(flted_12_3191:exists(v_bool_518_827':exists(v:exists(v_node_522_820':exists(v_bool_521_826':exists(n:exists(S1_3194:exists(v_3192:(x=v_node_522_820' & 
  res=v_node_522_820' & p_3189=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3193 & 
  m=v_3192 & self_3190=v_node_522_820' & 1+flted_12_3191=n & 
  v_bool_518_827'<=0 & (1+v)<=v_3192 & n<=-1 & v_node_522_820'!=null & 
  1<=v_bool_521_826' | x=v_node_522_820' & res=v_node_522_820' & 
  p_3189=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3193 & m=v_3192 & 
  self_3190=v_node_522_820' & 1+flted_12_3191=n & v_bool_518_827'<=0 & (1+
  v)<=v_3192 & v_node_522_820'!=null & 1<=v_bool_521_826' & 1<=n) & S!=() & 
  S=union(S1_3194,{v_3192})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_3194:exists(v_3192:v_3192<=v & S1_3194=S_3220 & 
  m_3258=m & (1+v)<=m & FGE(S_3220,m_3258) & S=union(S1_3194,{v_3192}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[Anon_43; n; 
                    S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{525}]&
                    (([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::ref [x]
                                EXISTS(flted_209_211,flted_209_212,Anon_44,
                                Anon_45,S1,
                                S2: x'::dll<Anon_44,flted_209_212,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                                res::dll<Anon_45,flted_209_211,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (
                                ([1=flted_209_212][1+flted_209_211=n]
                                 [S1!=() & GN(S,S1,S2)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_43; n; 
                  S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              EXISTS(flted_209_3391,flted_209_3392,Anon_3393,
                              Anon_3394,S1_3395,
                              S2_3396: x'::dll<Anon_3393,flted_209_3392,S1_3395>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_3394,flted_209_3391,S2_3396>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S1_3395!=() & union(S1_3395,S2_3396)=S]
                               [null!=x'][1+flted_209_3391=n & 0<=n]
                               [1=flted_209_3392]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_209_212:exists(q_3339:exists(tmp_213':exists(res:exists(q_3319:exists(v_node_214_1370':exists(Anon_43:exists(p_3315:exists(self_3316:exists(x':exists(n:exists(next_213_3337:exists(prev_213_1368':exists(x:exists(flted_209_211:exists(next_212_1365':exists(Anon_44:exists(Anon_45:exists(flted_12_3317:exists(S1_3320:exists(v_3318:exists(S1_3340:exists(v_3338:S1_3340= & 
  (flted_209_212=1 & q_3339=next_212_1365' & tmp_213'=v_node_214_1370' & 
  res=v_node_214_1370' & q_3319=v_node_214_1370' & Anon_43=p_3315 & 
  self_3316=Anon_45 & x'=Anon_45 & -1+n=flted_12_3317 & v_3338=v_3318 & 
  S1_3320=S2 & next_213_3337=next_212_1365' & prev_213_1368'=Anon_44 & 
  x=Anon_45 & flted_209_211=flted_12_3317 & next_212_1365'=null & 
  Anon_44=null & flted_12_3317<=-2 & Anon_45!=null | flted_209_212=1 & 
  q_3339=next_212_1365' & tmp_213'=v_node_214_1370' & res=v_node_214_1370' & 
  q_3319=v_node_214_1370' & Anon_43=p_3315 & self_3316=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_3317 & v_3338=v_3318 & S1_3320=S2 & 
  next_213_3337=next_212_1365' & prev_213_1368'=Anon_44 & x=Anon_45 & 
  flted_209_211=flted_12_3317 & next_212_1365'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_3317) & S=union(S1_3320,{v_3318}) & 
  S1=union(S1_3340,{v_3338}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[Anon_62; n; 
                    S](ex)x::dll<Anon_62,n,S>@M[Orig][LHSCase]@ rem br[{525}]&
                    (([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(flted_255_200,Anon_63,
                                S2: res::dll<Anon_63,flted_255_200,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([2+flted_255_200=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_62; n; 
                  S](ex)x::dll<Anon_62,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              EXISTS(flted_255_3491,Anon_3492,
                              S2_3493: res::dll<Anon_3492,flted_255_3491,S2_3493>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([2+flted_255_3491=n & 0<=n]
                               [S2_3493<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3468:exists(S1_3470:exists(S1_3427:exists(v_3425:S1_3427=union(S1_3470,
  {v_3468}) & S1_3427!=() & S2=S1_3470 & S!=() & S=union(S1_3427,
  {v_3425})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INSERT(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(p_198,m,
                                S1: x::dll<p_198,m,S1>@M[Orig][LHSCase]@ rem br[{525}]&
                                (
                                ([-1+m=n][S1!=() & INSERT(S,S1,a)][p=p_198]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(p_3658,m_3659,
                              S1_3660: x::dll<p_3658,m_3659,S1_3660>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_3660!=() & S1_3660=union(S,{a})][null!=x]
                               [p=p_3658][-1+m_3659=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3586:exists(v_3584:exists(S1_3572:exists(v_3570:exists(S1_3525:exists(v_3523:S1_3586= & 
  S1_3572=union(S1_3586,{v_3584}) & S1_3525= & v_3523=v_3570 & v_3584=a & 
  S1=union(S1_3572,{v_3570}) & S=union(S1_3525,{v_3523}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3613:exists(v_3611:exists(S1_3525:exists(v_3523:S1_3525!=() & 
  S1_3610!=() & v_3611=v_3523 & S1_3525=S_3553 & S1_3610=S1_3613 & 
  INSERT(S_3553,S1_3610,a) & S!=() & S1=union(S1_3613,{v_3611}) & 
  S=union(S1_3525,{v_3523})))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; n; 
                    S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 92::
                                EXISTS(p_175,n_176,
                                S2: x::dll<p_175,n_176,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([TRAV(S1,S2)][p=p_175][n=n_176]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 92::
                              EXISTS(p_5221,n_5222,
                              S2_5223: x::dll<p_5221,n_5222,S2_5223>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (([S1=S2_5223][n=n_5222 & 0<=n][p=p_5221]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_5181:exists(v_5179:exists(S1_5155:exists(v_5153:v_5179=v_5153 & 
  S1_5155=S1_5161 & S2_5178=S1_5181 & TRAV(S1_5161,S2_5178) & S1!=() & 
  S2=union(S1_5181,{v_5179}) & S1=union(S1_5155,
  {v_5153})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_39; m; 
                    S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{525}]&
                    (([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(flted_113_218,Anon_40,
                                S2: x'::dll<Anon_40,flted_113_218,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([1+flted_113_218=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39; m; 
                  S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{525}]&
                  (([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              EXISTS(flted_113_5415,Anon_5416,
                              S2_5417: x'::dll<Anon_5416,flted_113_5415,S2_5417>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([1+flted_113_5415=m & 0<=m]
                               [S2_5417<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5256:exists(v_5254:S1_5256= & S2= & S1=union(S1_5256,{v_5254}) & 
  S1!=()))) --> PF(S1,S2),
 (exists(q_5320:exists(q_5345:exists(Anon_39:exists(p_5251:exists(self_5317:exists(v_node_125_1454':exists(x:exists(res:exists(tmp_219':exists(v_5319:exists(S1_5321:exists(flted_12_5253:exists(m:exists(Anon_40:exists(self_5252:exists(q_5255:exists(flted_12_5318:exists(next_124_1453':exists(prev_122_1445':exists(v_bool_116_1455':exists(p_5316:exists(x':exists(flted_113_218:exists(S1_5346:exists(v_5344:exists(S1_5256:exists(v_5254:S1_5256!=() & 
  S1_5256=union(S1_5321,{v_5319}) & (q_5320=q_5345 & Anon_39=p_5251 & 
  self_5317=x' & v_node_125_1454'=p_5316 & x=p_5316 & res=p_5316 & 
  tmp_219'=p_5316 & v_5344=v_5319 & S1_5321=S1_5346 & 
  flted_12_5253=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1445' & self_5252=p_5316 & q_5255=x' & 1+
  flted_12_5318=flted_113_218 & next_124_1453'=null & prev_122_1445'=null & 
  flted_113_218<=-2 & v_bool_116_1455'<=0 & p_5316!=null & x'!=null | 
  q_5320=q_5345 & Anon_39=p_5251 & self_5317=x' & v_node_125_1454'=p_5316 & 
  x=p_5316 & res=p_5316 & tmp_219'=p_5316 & v_5344=v_5319 & 
  S1_5321=S1_5346 & flted_12_5253=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1445' & self_5252=p_5316 & q_5255=x' & 1+
  flted_12_5318=flted_113_218 & next_124_1453'=null & prev_122_1445'=null & 
  v_bool_116_1455'<=0 & p_5316!=null & x'!=null & 1<=flted_113_218) & 
  S1!=() & S2=union(S1_5346,{v_5344}) & S1=union(S1_5256,
  {v_5254}))))))))))))))))))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  PUF(S1,S)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_36; n; 
                    S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(v_220,n_221,Anon_37,q,Anon_38,
                                S1: x'::node<v_220,Anon_37,q>@M[Orig][] * 
                                q::dll<Anon_38,n_221,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([PUF(S1,S)][v=v_220][n=n_221][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36; n; 
                  S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(v_5530,n_5531,Anon_5532,q_5533,
                              Anon_5534,
                              S1_5535: x'::node<v_5530,Anon_5532,q_5533>@M[Orig][] * 
                              q_5533::dll<Anon_5534,n_5531,S1_5535>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S1_5535][x'!=null][n=n_5531 & 0<=n]
                               [v=v_5530]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> PUF(S1,S),
 (exists(q_5457:exists(q_5475:exists(v:exists(v_220:exists(n:exists(Anon_38:exists(p_5453:exists(Anon_37:exists(Anon_36:exists(self_5454:exists(q:exists(x':exists(flted_12_5455:exists(v_bool_97_1476':exists(x:exists(tmp_222':exists(n_221:exists(S1_5458:exists(v_5456:exists(S1_5476:exists(v_5474:(q_5457=q_5475 & 
  v=v_220 & n=n_221 & v_5474=v_5456 & S1_5458=S1_5476 & Anon_38=Anon_36 & 
  p_5453=Anon_36 & Anon_37=Anon_36 & self_5454=x & q=x & x'=tmp_222' & 1+
  flted_12_5455=n_221 & n_221<=-1 & v_bool_97_1476'<=0 & x!=null & 
  tmp_222'!=null | q_5457=q_5475 & v=v_220 & n=n_221 & v_5474=v_5456 & 
  S1_5458=S1_5476 & Anon_38=Anon_36 & p_5453=Anon_36 & Anon_37=Anon_36 & 
  self_5454=x & q=x & x'=tmp_222' & 1+flted_12_5455=n_221 & 
  v_bool_97_1476'<=0 & x!=null & tmp_222'!=null & 1<=n_221) & S!=() & 
  S=union(S1_5458,{v_5456}) & S1=union(S1_5476,
  {v_5474}))))))))))))))))))))))) --> PUF(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_41; n; 
                    S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(n_214,Anon_42,
                                S2: x::dll<Anon_42,n_214,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([n=n_214]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_41; n; 
                  S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              EXISTS(Anon_5541,n_5542,
                              S2_5543: x::dll<Anon_5541,n_5542,S2_5543>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([n=n_5542 & 0<=n][S1=S2_5543][res=x]
                               [Anon_5541=Anon_41]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SN(S,S2)
!!! POST:  S=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                    Anon_49; j; 
                    S](ex)EXISTS(x_205: x::node<v,Anon_46,t>@M[Orig][] * 
                    t::dll<x_205,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                    y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                    ([x=x_205 & x!=null][0<=Anon_47][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::ref [x]
                                EXISTS(v_206,y_207,j_208,Anon_50,Anon_51,
                                S2: x::node<v_206,Anon_50,y_207>@M[Orig][] * 
                                y::dll<Anon_51,j_208,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (
                                ([SN(S,S2)][v=v_206][y=y_207][j=j_208]
                                 [x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                  Anon_49; j; S](ex)x::node<v,Anon_46,t>@M[Orig][] * 
                  t::dll<x_205,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                  y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ([x=x_205 & x!=null][0<=Anon_47]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::ref [x]
                              EXISTS(v_6048,y_6049,j_6050,Anon_6052,
                              S2_6053: y::dll<Anon_6052,j_6050,S2_6053>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S2_6053][x!=null][j=j_6050 & 0<=j]
                               [y=y_6049][v=v_6048][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S) --> SN(S,S2),
 (S=S2 & S2=) --> SN(S,S2),
 (exists(q_5974:exists(q_5990:exists(Anon_50:exists(Anon_46:exists(x_5923:exists(x':exists(self_5971:exists(p_5970:exists(Anon_49:exists(j:exists(v:exists(v_206:exists(y_207:exists(x:exists(flted_12_5972:exists(v_bool_224_1342':exists(y:exists(Anon_51:exists(Anon_47:exists(j_208:exists(S1_5975:exists(v_5973:exists(S1_5991:exists(v_5989:(q_5974=q_5990 & 
  Anon_50=Anon_46 & x_5923=Anon_51 & x'=Anon_51 & self_5971=y & 
  p_5970=Anon_49 & v_5989=v_5973 & S1_5975=S1_5991 & j=j_208 & v=v_206 & 
  y_207=y & x=Anon_51 & 1+flted_12_5972=j_208 & j_208<=-1 & 
  v_bool_224_1342'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 | 
  q_5974=q_5990 & Anon_50=Anon_46 & x_5923=Anon_51 & x'=Anon_51 & 
  self_5971=y & p_5970=Anon_49 & v_5989=v_5973 & S1_5975=S1_5991 & j=j_208 & 
  v=v_206 & y_207=y & x=Anon_51 & 1+flted_12_5972=j_208 & 
  v_bool_224_1342'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 & 1<=j_208) & 
  S!=() & S=union(S1_5975,{v_5973}) & S2=union(S1_5991,
  {v_5989})))))))))))))))))))))))))) --> SN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::ref [x]
                                EXISTS(p_178,Anon_70,n2,n1,S1,
                                S2: x'::dll<p_178,n1,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                                res::dll<Anon_70,n2,S2>@M[Orig][LHSCase]@ rem br[{525}]&
                                (
                                ([a=n1 & 0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][p=p_178]
                                 [null!=x'][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 85::ref [x]
                              EXISTS(p_6890,Anon_6891,n2_6892,n1_6893,
                              S1_6894,
                              S2_6895: x'::dll<p_6890,n1_6893,S1_6894>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_6891,n2_6892,S2_6895>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_6894!=() & S2_6895!=() & union(S1_6894,
                                 S2_6895)=S]
                               [null!=res][null!=x'][p=p_6890]
                               [a=n1_6893 & 0!=n1_6893 & 0<=n & n=n1_6893+
                                 n2_6892 & 0!=n2_6892]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_6684:exists(v_6682:exists(S1_6779:exists(v_6777:S1_6684!=() & 
  S1_6779= & v_6682=v_6777 & S2=S1_6684 & S=union(S1_6684,{v_6682}) & 
  S!=() & S1=union(S1_6779,{v_6777})))))) --> SPLIT(S,S1,S2),
 (exists(S1_6823:exists(v_6821:exists(S1_6733:exists(v_6731:S1_6733!=() & 
  S2_6818!=() & S1_6817!=() & v_6821=v_6731 & S1_6733=S_6736 & 
  S1_6817=S1_6823 & S2_6818=S2 & SPLIT(S_6736,S1_6817,S2_6818) & S!=() & 
  S1=union(S1_6823,{v_6821}) & S=union(S1_6733,
  {v_6731})))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                    S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                    y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_225,n_226,Anon_32,S3,Anon_33,
                                S4: x'::dll<Anon_32,m_225,S3>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                                y'::dll<Anon_33,n_226,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([m=m_225][n=n_226]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                  S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                  y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(Anon_6907,m_6908,S3_6909,Anon_6910,
                              n_6911,
                              S4_6912: x'::dll<Anon_6907,m_6908,S3_6909>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                              y'::dll<Anon_6910,n_6911,S4_6912>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([m=m_6908 & 0<=m][n=n_6911 & 0<=n][S1=S4_6912]
                               [S2=S3_6909][y=x'][x=y'][Anon_6907=Anon_31]
                               [Anon_6910=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (543,6)  (239,13)  (239,4)  (342,4)  (342,11)  (352,6)  (352,13)  (351,6)  (351,6)  (349,6)  (349,13)  (348,8)  (347,27)  (347,14)  (347,9)  (346,10)  (346,4)  (345,8)  (345,12)  (345,4)  (345,4) )

Total verification time: 10.67 second(s)
	Time spent in main process: 0.85 second(s)
	Time spent in child processes: 9.82 second(s)
