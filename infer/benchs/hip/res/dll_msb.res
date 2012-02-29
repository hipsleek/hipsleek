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
                              EXISTS(q_2045,t_2046,
                              S_2047: x::dll<q_2045,t_2046,S_2047>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S_2047=union(S1,S2)][q=q_2045]
                               [t_2046=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1937:exists(v_1782:exists(v_1935:exists(S1_1784:S1!=() & S2= & 
  S=union(S1_1937,{v_1935}) & S1=union(S1_1784,{v_1782}) & S1_1937=S2 & 
  v_1782=v_1935 & S1_1784=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1781:exists(m:exists(p_1779:exists(q_215:exists(q:exists(self_1842:exists(p_1841:exists(p:exists(v_1895:exists(S1_1897:exists(n:exists(q_1845:exists(q_1896:exists(q_1882:exists(x:exists(flted_12_1843:exists(q_1783:exists(y:exists(self_1780:exists(v_bool_184_1409':exists(v_bool_182_1414':exists(t:exists(S1_1883:exists(v_1881:exists(S1_1784:exists(v_1782:exists(S1_1846:exists(v_1844:S1_1883=union(S1_1897,
  {v_1895}) & S1_1784= & (flted_12_1781=0 & m=1 & p_1779=q & q_215=q & 
  self_1842=y & p_1841=p & v_1881=v_1782 & v_1895=v_1844 & S1_1846=S1_1897 & 
  1+n=t & q_1845=q_1896 & q_1882=y & x=self_1780 & 2+flted_12_1843=t & 
  q_1783=null & t<=0 & y!=null & self_1780!=null & 1<=v_bool_184_1409' & 
  1<=v_bool_182_1414' | flted_12_1781=0 & m=1 & p_1779=q & q_215=q & 
  self_1842=y & p_1841=p & v_1881=v_1782 & v_1895=v_1844 & S1_1846=S1_1897 & 
  1+n=t & q_1845=q_1896 & q_1882=y & x=self_1780 & 2+flted_12_1843=t & 
  q_1783=null & y!=null & self_1780!=null & 1<=v_bool_184_1409' & 
  1<=v_bool_182_1414' & 2<=t) & S2!=() & S=union(S1_1883,{v_1881}) & 
  S1=union(S1_1784,{v_1782}) & S2=union(S1_1846,{v_1844}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1784:exists(v_1782:exists(S1_1937:exists(v_1935:S1_1784= & 
  v_1782=v_1935 & S2=S1_1937 & S1=union(S1_1784,{v_1782}) & S=union(S1_1937,
  {v_1935}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1967:exists(v_1965:exists(S1_1784:exists(v_1782:S_1964!=() & 
  S1_1784!=() & S1_1784=S1_1855 & v_1782=v_1965 & S_1964=S1_1967 & 
  S2_1858=S2 & APP2(S_1964,S1_1855,S2_1858) & S1!=() & S=union(S1_1967,
  {v_1965}) & S1=union(S1_1784,{v_1782})))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
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
                              EXISTS(p_2742,m_2743,
                              S1_2744: x::dll<p_2742,m_2743,S1_2744>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (([p=p_2742][S1_2744<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2604:exists(v_2602:exists(S1_2477:exists(v_2475:exists(S1_2395:exists(v_2393:exists(S1_2590:exists(v_2588:exists(S1_2350:exists(v_2348:S1_2477=S1_2604 & 
  v_2602=v_2475 & S1_2590=union(S1_2604,{v_2602}) & S1_2395!=() & 
  S1_2350!=() & S1_2395=union(S1_2477,{v_2475}) & S1_2350=union(S1_2395,
  {v_2393}) & v_2348=v_2588 & S!=() & S1=union(S1_2590,{v_2588}) & 
  S=union(S1_2350,{v_2348})))))))))))) --> DEL(S,S1),
 (exists(S1_2395:exists(v_2393:exists(S1_2653:exists(v_2651:exists(S1_2350:exists(v_2348:S1_2395= & 
  S1_2350!=() & S1_2350=union(S1_2395,{v_2393}) & S1_2653= & v_2651=v_2348 & 
  S1=union(S1_2653,{v_2651}) & S!=() & S=union(S1_2350,
  {v_2348})))))))) --> DEL(S,S1),
 (exists(m:exists(flted_12_2537:exists(n:exists(a:exists(q_2539:exists(p_2535:exists(p:exists(p_195:exists(x:exists(p_2553:exists(v_int_295_2676:exists(n_2554:exists(tmp_197':exists(v_bool_283_1223':exists(self_2536:exists(m_2674:exists(q_2678:exists(S1_2540:exists(v_2538:exists(S1_2679:exists(v_2677:S1_2540!=() & 
  S1_2675!=() & (-1+m=m_2674 & flted_12_2537=n_2554 & -1+n=n_2554 & -1+
  a=v_int_295_2676 & q_2539=q_2678 & S1_2675=S1_2679 & S1_2540=S_2555 & 
  v_2677=v_2538 & p_2535=p_195 & p=p_195 & x=self_2536 & p_2553=self_2536 & 
  1<=v_int_295_2676 & (1+v_int_295_2676)<=n_2554 & m_2674<=-1 & 
  tmp_197'=null & !(v_bool_283_1223') & self_2536!=null & q_2678!=null & 
  DEL(S_2555,S1_2675) | -1+m=m_2674 & flted_12_2537=n_2554 & -1+n=n_2554 & 
  -1+a=v_int_295_2676 & q_2539=q_2678 & S1_2675=S1_2679 & S1_2540=S_2555 & 
  v_2677=v_2538 & p_2535=p_195 & p=p_195 & x=self_2536 & p_2553=self_2536 & 
  1<=v_int_295_2676 & (1+v_int_295_2676)<=n_2554 & tmp_197'=null & 
  !(v_bool_283_1223') & self_2536!=null & 1<=m_2674 & q_2678!=null & 
  DEL(S_2555,S1_2675)) & S!=() & S=union(S1_2540,{v_2538}) & 
  S1=union(S1_2679,{v_2677}))))))))))))))))))))))) --> DEL(S,S1)]
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
                              or EXISTS(Anon_3297,Anon_3298,
                                 m_3299: res::node<m_3299,Anon_3297,Anon_3298>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_3299 & m_3299 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_3204:exists(Anon_75:exists(Anon_76:exists(Anon_77:exists(q_3208:exists(self_3205:exists(flted_12_3206:exists(v_bool_518_827':exists(v:exists(v_node_522_820':exists(v_bool_521_826':exists(n:exists(S1_3209:exists(v_3207:(x=v_node_522_820' & 
  res=v_node_522_820' & p_3204=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3208 & 
  m=v_3207 & self_3205=v_node_522_820' & 1+flted_12_3206=n & 
  v_bool_518_827'<=0 & (1+v)<=v_3207 & n<=-1 & v_node_522_820'!=null & 
  1<=v_bool_521_826' | x=v_node_522_820' & res=v_node_522_820' & 
  p_3204=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3208 & m=v_3207 & 
  self_3205=v_node_522_820' & 1+flted_12_3206=n & v_bool_518_827'<=0 & (1+
  v)<=v_3207 & v_node_522_820'!=null & 1<=v_bool_521_826' & 1<=n) & S!=() & 
  S=union(S1_3209,{v_3207})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_3209:exists(v_3207:v_3207<=v & S1_3209=S_3235 & 
  m_3273=m & (1+v)<=m & FGE(S_3235,m_3273) & S=union(S1_3209,{v_3207}) & 
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
                              EXISTS(flted_209_3406,flted_209_3407,Anon_3408,
                              Anon_3409,S1_3410,
                              S2_3411: x'::dll<Anon_3408,flted_209_3407,S1_3410>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_3409,flted_209_3406,S2_3411>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S1_3410!=() & union(S1_3410,S2_3411)=S]
                               [null!=x'][1+flted_209_3406=n & 0<=n]
                               [1=flted_209_3407]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_209_212:exists(q_3354:exists(tmp_213':exists(res:exists(q_3334:exists(v_node_214_1370':exists(Anon_43:exists(p_3330:exists(self_3331:exists(x':exists(n:exists(next_213_3352:exists(prev_213_1368':exists(x:exists(flted_209_211:exists(next_212_1365':exists(Anon_44:exists(Anon_45:exists(flted_12_3332:exists(S1_3335:exists(v_3333:exists(S1_3355:exists(v_3353:S1_3355= & 
  (flted_209_212=1 & q_3354=next_212_1365' & tmp_213'=v_node_214_1370' & 
  res=v_node_214_1370' & q_3334=v_node_214_1370' & Anon_43=p_3330 & 
  self_3331=Anon_45 & x'=Anon_45 & -1+n=flted_12_3332 & v_3353=v_3333 & 
  S1_3335=S2 & next_213_3352=next_212_1365' & prev_213_1368'=Anon_44 & 
  x=Anon_45 & flted_209_211=flted_12_3332 & next_212_1365'=null & 
  Anon_44=null & flted_12_3332<=-2 & Anon_45!=null | flted_209_212=1 & 
  q_3354=next_212_1365' & tmp_213'=v_node_214_1370' & res=v_node_214_1370' & 
  q_3334=v_node_214_1370' & Anon_43=p_3330 & self_3331=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_3332 & v_3353=v_3333 & S1_3335=S2 & 
  next_213_3352=next_212_1365' & prev_213_1368'=Anon_44 & x=Anon_45 & 
  flted_209_211=flted_12_3332 & next_212_1365'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_3332) & S=union(S1_3335,{v_3333}) & 
  S1=union(S1_3355,{v_3353}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
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
                              EXISTS(flted_255_3506,Anon_3507,
                              S2_3508: res::dll<Anon_3507,flted_255_3506,S2_3508>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([2+flted_255_3506=n & 0<=n]
                               [S2_3508<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3483:exists(S1_3485:exists(S1_3442:exists(v_3440:S1_3442=union(S1_3485,
  {v_3483}) & S1_3442!=() & S2=S1_3485 & S!=() & S=union(S1_3442,
  {v_3440})))))) --> GNN(S,S2)]
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
                              EXISTS(p_3673,m_3674,
                              S1_3675: x::dll<p_3673,m_3674,S1_3675>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_3675!=() & S1_3675=union(S,{a})][null!=x]
                               [p=p_3673][-1+m_3674=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3601:exists(v_3599:exists(S1_3587:exists(v_3585:exists(S1_3540:exists(v_3538:S1_3601= & 
  S1_3587=union(S1_3601,{v_3599}) & S1_3540= & v_3538=v_3585 & v_3599=a & 
  S1=union(S1_3587,{v_3585}) & S=union(S1_3540,{v_3538}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3628:exists(v_3626:exists(S1_3540:exists(v_3538:S1_3540!=() & 
  S1_3625!=() & v_3626=v_3538 & S1_3540=S_3568 & S1_3625=S1_3628 & 
  INSERT(S_3568,S1_3625,a) & S!=() & S1=union(S1_3628,{v_3626}) & 
  S=union(S1_3540,{v_3538})))))) --> INSERT(S,S1,a)]
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
                              EXISTS(p_5236,n_5237,
                              S2_5238: x::dll<p_5236,n_5237,S2_5238>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (([S1=S2_5238][n=n_5237 & 0<=n][p=p_5236]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_5196:exists(v_5194:exists(S1_5170:exists(v_5168:v_5194=v_5168 & 
  S1_5170=S1_5176 & S2_5193=S1_5196 & TRAV(S1_5176,S2_5193) & S1!=() & 
  S2=union(S1_5196,{v_5194}) & S1=union(S1_5170,
  {v_5168})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_113_5430,Anon_5431,
                              S2_5432: x'::dll<Anon_5431,flted_113_5430,S2_5432>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([1+flted_113_5430=m & 0<=m]
                               [S2_5432<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5271:exists(v_5269:S1_5271= & S2= & S1=union(S1_5271,{v_5269}) & 
  S1!=()))) --> PF(S1,S2),
 (exists(q_5335:exists(q_5360:exists(Anon_39:exists(p_5266:exists(self_5332:exists(v_node_125_1454':exists(x:exists(res:exists(tmp_219':exists(v_5334:exists(S1_5336:exists(flted_12_5268:exists(m:exists(Anon_40:exists(self_5267:exists(q_5270:exists(flted_12_5333:exists(next_124_1453':exists(prev_122_1445':exists(v_bool_116_1455':exists(p_5331:exists(x':exists(flted_113_218:exists(S1_5361:exists(v_5359:exists(S1_5271:exists(v_5269:S1_5271!=() & 
  S1_5271=union(S1_5336,{v_5334}) & (q_5335=q_5360 & Anon_39=p_5266 & 
  self_5332=x' & v_node_125_1454'=p_5331 & x=p_5331 & res=p_5331 & 
  tmp_219'=p_5331 & v_5359=v_5334 & S1_5336=S1_5361 & 
  flted_12_5268=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1445' & self_5267=p_5331 & q_5270=x' & 1+
  flted_12_5333=flted_113_218 & next_124_1453'=null & prev_122_1445'=null & 
  flted_113_218<=-2 & v_bool_116_1455'<=0 & p_5331!=null & x'!=null | 
  q_5335=q_5360 & Anon_39=p_5266 & self_5332=x' & v_node_125_1454'=p_5331 & 
  x=p_5331 & res=p_5331 & tmp_219'=p_5331 & v_5359=v_5334 & 
  S1_5336=S1_5361 & flted_12_5268=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1445' & self_5267=p_5331 & q_5270=x' & 1+
  flted_12_5333=flted_113_218 & next_124_1453'=null & prev_122_1445'=null & 
  v_bool_116_1455'<=0 & p_5331!=null & x'!=null & 1<=flted_113_218) & 
  S1!=() & S2=union(S1_5361,{v_5359}) & S1=union(S1_5271,
  {v_5269}))))))))))))))))))))))))))))) --> PF(S1,S2)]
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
                              EXISTS(v_5545,n_5546,Anon_5547,q_5548,
                              Anon_5549,
                              S1_5550: x'::node<v_5545,Anon_5547,q_5548>@M[Orig][] * 
                              q_5548::dll<Anon_5549,n_5546,S1_5550>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S1_5550][x'!=null][n=n_5546 & 0<=n]
                               [v=v_5545]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> PUF(S1,S),
 (exists(q_5472:exists(q_5490:exists(v:exists(v_220:exists(n:exists(Anon_38:exists(p_5468:exists(Anon_37:exists(Anon_36:exists(self_5469:exists(q:exists(x':exists(flted_12_5470:exists(v_bool_97_1476':exists(x:exists(tmp_222':exists(n_221:exists(S1_5473:exists(v_5471:exists(S1_5491:exists(v_5489:(q_5472=q_5490 & 
  v=v_220 & n=n_221 & v_5489=v_5471 & S1_5473=S1_5491 & Anon_38=Anon_36 & 
  p_5468=Anon_36 & Anon_37=Anon_36 & self_5469=x & q=x & x'=tmp_222' & 1+
  flted_12_5470=n_221 & n_221<=-1 & v_bool_97_1476'<=0 & x!=null & 
  tmp_222'!=null | q_5472=q_5490 & v=v_220 & n=n_221 & v_5489=v_5471 & 
  S1_5473=S1_5491 & Anon_38=Anon_36 & p_5468=Anon_36 & Anon_37=Anon_36 & 
  self_5469=x & q=x & x'=tmp_222' & 1+flted_12_5470=n_221 & 
  v_bool_97_1476'<=0 & x!=null & tmp_222'!=null & 1<=n_221) & S!=() & 
  S=union(S1_5473,{v_5471}) & S1=union(S1_5491,
  {v_5489}))))))))))))))))))))))) --> PUF(S1,S)]
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
                              EXISTS(Anon_5556,n_5557,
                              S2_5558: x::dll<Anon_5556,n_5557,S2_5558>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([n=n_5557 & 0<=n][S1=S2_5558][res=x]
                               [Anon_5556=Anon_41]))&
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
                              EXISTS(v_6063,y_6064,j_6065,Anon_6067,
                              S2_6068: y::dll<Anon_6067,j_6065,S2_6068>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S2_6068][x!=null][j=j_6065 & 0<=j]
                               [y=y_6064][v=v_6063][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S) --> SN(S,S2),
 (S=S2 & S2=) --> SN(S,S2),
 (exists(q_5989:exists(q_6005:exists(Anon_50:exists(Anon_46:exists(x_5938:exists(x':exists(self_5986:exists(p_5985:exists(Anon_49:exists(j:exists(v:exists(v_206:exists(y_207:exists(x:exists(flted_12_5987:exists(v_bool_224_1342':exists(y:exists(Anon_51:exists(Anon_47:exists(j_208:exists(S1_5990:exists(v_5988:exists(S1_6006:exists(v_6004:(q_5989=q_6005 & 
  Anon_50=Anon_46 & x_5938=Anon_51 & x'=Anon_51 & self_5986=y & 
  p_5985=Anon_49 & v_6004=v_5988 & S1_5990=S1_6006 & j=j_208 & v=v_206 & 
  y_207=y & x=Anon_51 & 1+flted_12_5987=j_208 & j_208<=-1 & 
  v_bool_224_1342'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 | 
  q_5989=q_6005 & Anon_50=Anon_46 & x_5938=Anon_51 & x'=Anon_51 & 
  self_5986=y & p_5985=Anon_49 & v_6004=v_5988 & S1_5990=S1_6006 & j=j_208 & 
  v=v_206 & y_207=y & x=Anon_51 & 1+flted_12_5987=j_208 & 
  v_bool_224_1342'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 & 1<=j_208) & 
  S!=() & S=union(S1_5990,{v_5988}) & S2=union(S1_6006,
  {v_6004})))))))))))))))))))))))))) --> SN(S,S2)]
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
                              EXISTS(p_6905,Anon_6906,n2_6907,n1_6908,
                              S1_6909,
                              S2_6910: x'::dll<p_6905,n1_6908,S1_6909>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_6906,n2_6907,S2_6910>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_6909!=() & S2_6910!=() & union(S1_6909,
                                 S2_6910)=S]
                               [null!=res][null!=x'][p=p_6905]
                               [a=n1_6908 & 0!=n1_6908 & 0<=n & n=n1_6908+
                                 n2_6907 & 0!=n2_6907]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_6699:exists(v_6697:exists(S1_6794:exists(v_6792:S1_6699!=() & 
  S1_6794= & v_6697=v_6792 & S2=S1_6699 & S=union(S1_6699,{v_6697}) & 
  S!=() & S1=union(S1_6794,{v_6792})))))) --> SPLIT(S,S1,S2),
 (exists(S1_6838:exists(v_6836:exists(S1_6748:exists(v_6746:S1_6748!=() & 
  S2_6833!=() & S1_6832!=() & v_6836=v_6746 & S1_6748=S_6751 & 
  S1_6832=S1_6838 & S2_6833=S2 & SPLIT(S_6751,S1_6832,S2_6833) & S!=() & 
  S1=union(S1_6838,{v_6836}) & S=union(S1_6748,
  {v_6746})))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(Anon_6922,m_6923,S3_6924,Anon_6925,
                              n_6926,
                              S4_6927: x'::dll<Anon_6922,m_6923,S3_6924>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                              y'::dll<Anon_6925,n_6926,S4_6927>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([m=m_6923 & 0<=m][n=n_6926 & 0<=n][S1=S4_6927]
                               [S2=S3_6924][y=x'][x=y'][Anon_6922=Anon_31]
                               [Anon_6925=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (543,6)  (239,13)  (239,4)  (342,4)  (342,11)  (352,6)  (352,13)  (351,6)  (351,6)  (349,6)  (349,13)  (348,8)  (347,27)  (347,14)  (347,9)  (346,10)  (346,4)  (345,8)  (345,12)  (345,4)  (345,4) )

Total verification time: 10.63 second(s)
	Time spent in main process: 0.85 second(s)
	Time spent in child processes: 9.78 second(s)
