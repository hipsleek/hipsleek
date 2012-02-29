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
!!! POST:  union(S1,S2)=S
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
                              EXISTS(q_2046,t_2047,
                              S_2048: x::dll<q_2046,t_2047,S_2048>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([union(S1,S2)=S_2048][q=q_2046]
                               [t_2047=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1938:exists(v_1783:exists(v_1936:exists(S1_1785:S1!=() & S2= & 
  S=union(S1_1938,{v_1936}) & S1=union(S1_1785,{v_1783}) & S1_1938=S2 & 
  v_1783=v_1936 & S1_1785=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1782:exists(m:exists(p_1780:exists(q_215:exists(q:exists(self_1843:exists(p_1842:exists(p:exists(v_1896:exists(S1_1898:exists(n:exists(q_1846:exists(q_1897:exists(q_1883:exists(x:exists(flted_12_1844:exists(q_1784:exists(y:exists(self_1781:exists(v_bool_184_1410':exists(v_bool_182_1415':exists(t:exists(S1_1884:exists(v_1882:exists(S1_1785:exists(v_1783:exists(S1_1847:exists(v_1845:S1_1884=union(S1_1898,
  {v_1896}) & S1_1785= & (flted_12_1782=0 & m=1 & p_1780=q & q_215=q & 
  self_1843=y & p_1842=p & v_1882=v_1783 & v_1896=v_1845 & S1_1847=S1_1898 & 
  1+n=t & q_1846=q_1897 & q_1883=y & x=self_1781 & 2+flted_12_1844=t & 
  q_1784=null & t<=0 & y!=null & self_1781!=null & 1<=v_bool_184_1410' & 
  1<=v_bool_182_1415' | flted_12_1782=0 & m=1 & p_1780=q & q_215=q & 
  self_1843=y & p_1842=p & v_1882=v_1783 & v_1896=v_1845 & S1_1847=S1_1898 & 
  1+n=t & q_1846=q_1897 & q_1883=y & x=self_1781 & 2+flted_12_1844=t & 
  q_1784=null & y!=null & self_1781!=null & 1<=v_bool_184_1410' & 
  1<=v_bool_182_1415' & 2<=t) & S2!=() & S=union(S1_1884,{v_1882}) & 
  S1=union(S1_1785,{v_1783}) & S2=union(S1_1847,{v_1845}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1785:exists(v_1783:exists(S1_1938:exists(v_1936:S1_1785= & 
  v_1783=v_1936 & S2=S1_1938 & S1=union(S1_1785,{v_1783}) & S=union(S1_1938,
  {v_1936}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1968:exists(v_1966:exists(S1_1785:exists(v_1783:S_1965!=() & 
  S1_1785!=() & S1_1785=S1_1856 & v_1783=v_1966 & S_1965=S1_1968 & 
  S2_1859=S2 & APP2(S_1965,S1_1856,S2_1859) & S1!=() & S=union(S1_1968,
  {v_1966}) & S1=union(S1_1785,{v_1783})))))) --> APP2(S,S1,S2)]
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
                              or EXISTS(Anon_3250,Anon_3251,
                                 m_3252: res::node<m_3252,Anon_3250,Anon_3251>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_3252 & m_3252 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_3157:exists(Anon_75:exists(Anon_76:exists(Anon_77:exists(q_3161:exists(self_3158:exists(flted_12_3159:exists(v_bool_518_827':exists(v:exists(v_node_522_820':exists(v_bool_521_826':exists(n:exists(S1_3162:exists(v_3160:(x=v_node_522_820' & 
  res=v_node_522_820' & p_3157=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3161 & 
  m=v_3160 & self_3158=v_node_522_820' & 1+flted_12_3159=n & 
  v_bool_518_827'<=0 & (1+v)<=v_3160 & n<=-1 & v_node_522_820'!=null & 
  1<=v_bool_521_826' | x=v_node_522_820' & res=v_node_522_820' & 
  p_3157=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3161 & m=v_3160 & 
  self_3158=v_node_522_820' & 1+flted_12_3159=n & v_bool_518_827'<=0 & (1+
  v)<=v_3160 & v_node_522_820'!=null & 1<=v_bool_521_826' & 1<=n) & S!=() & 
  S=union(S1_3162,{v_3160})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_3162:exists(v_3160:v_3160<=v & S1_3162=S_3188 & 
  m_3226=m & (1+v)<=m & FGE(S_3188,m_3226) & S=union(S1_3162,{v_3160}) & 
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
                              EXISTS(flted_209_3359,flted_209_3360,Anon_3361,
                              Anon_3362,S1_3363,
                              S2_3364: x'::dll<Anon_3361,flted_209_3360,S1_3363>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_3362,flted_209_3359,S2_3364>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S1_3363!=() & union(S1_3363,S2_3364)=S]
                               [null!=x'][1+flted_209_3359=n & 0<=n]
                               [1=flted_209_3360]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_209_212:exists(q_3307:exists(tmp_213':exists(res:exists(q_3287:exists(v_node_214_1371':exists(Anon_43:exists(p_3283:exists(self_3284:exists(x':exists(n:exists(next_213_3305:exists(prev_213_1369':exists(x:exists(flted_209_211:exists(next_212_1366':exists(Anon_44:exists(Anon_45:exists(flted_12_3285:exists(S1_3288:exists(v_3286:exists(S1_3308:exists(v_3306:S1_3308= & 
  (flted_209_212=1 & q_3307=next_212_1366' & tmp_213'=v_node_214_1371' & 
  res=v_node_214_1371' & q_3287=v_node_214_1371' & Anon_43=p_3283 & 
  self_3284=Anon_45 & x'=Anon_45 & -1+n=flted_12_3285 & v_3306=v_3286 & 
  S1_3288=S2 & next_213_3305=next_212_1366' & prev_213_1369'=Anon_44 & 
  x=Anon_45 & flted_209_211=flted_12_3285 & next_212_1366'=null & 
  Anon_44=null & flted_12_3285<=-2 & Anon_45!=null | flted_209_212=1 & 
  q_3307=next_212_1366' & tmp_213'=v_node_214_1371' & res=v_node_214_1371' & 
  q_3287=v_node_214_1371' & Anon_43=p_3283 & self_3284=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_3285 & v_3306=v_3286 & S1_3288=S2 & 
  next_213_3305=next_212_1366' & prev_213_1369'=Anon_44 & x=Anon_45 & 
  flted_209_211=flted_12_3285 & next_212_1366'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_3285) & S=union(S1_3288,{v_3286}) & 
  S1=union(S1_3308,{v_3306}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
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
                              EXISTS(flted_255_3459,Anon_3460,
                              S2_3461: res::dll<Anon_3460,flted_255_3459,S2_3461>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([2+flted_255_3459=n & 0<=n]
                               [S2_3461<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3436:exists(S1_3438:exists(S1_3395:exists(v_3393:S1_3395=union(S1_3438,
  {v_3436}) & S1_3395!=() & S2=S1_3438 & S!=() & S=union(S1_3395,
  {v_3393})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              EXISTS(p_3626,m_3627,
                              S1_3628: x::dll<p_3626,m_3627,S1_3628>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_3628!=() & S1_3628=union(S,{a})][null!=x]
                               [p=p_3626][-1+m_3627=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3554:exists(v_3552:exists(S1_3540:exists(v_3538:exists(S1_3493:exists(v_3491:S1_3554= & 
  S1_3540=union(S1_3554,{v_3552}) & S1_3493= & v_3491=v_3538 & v_3552=a & 
  S1=union(S1_3540,{v_3538}) & S=union(S1_3493,{v_3491}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3581:exists(v_3579:exists(S1_3493:exists(v_3491:S1_3493!=() & 
  S1_3578!=() & v_3579=v_3491 & S1_3493=S_3521 & S1_3578=S1_3581 & 
  INSERT(S_3521,S1_3578,a) & S!=() & S1=union(S1_3581,{v_3579}) & 
  S=union(S1_3493,{v_3491})))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              EXISTS(p_5189,n_5190,
                              S2_5191: x::dll<p_5189,n_5190,S2_5191>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (([S1=S2_5191][n=n_5190 & 0<=n][p=p_5189]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_5149:exists(v_5147:exists(S1_5123:exists(v_5121:v_5147=v_5121 & 
  S1_5123=S1_5129 & S2_5146=S1_5149 & TRAV(S1_5129,S2_5146) & S1!=() & 
  S2=union(S1_5149,{v_5147}) & S1=union(S1_5123,
  {v_5121})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_113_5383,Anon_5384,
                              S2_5385: x'::dll<Anon_5384,flted_113_5383,S2_5385>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([1+flted_113_5383=m & 0<=m]
                               [S2_5385<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5224:exists(v_5222:S1_5224= & S2= & S1=union(S1_5224,{v_5222}) & 
  S1!=()))) --> PF(S1,S2),
 (exists(q_5288:exists(q_5313:exists(Anon_39:exists(p_5219:exists(self_5285:exists(v_node_125_1455':exists(x:exists(res:exists(tmp_219':exists(v_5287:exists(S1_5289:exists(flted_12_5221:exists(m:exists(Anon_40:exists(self_5220:exists(q_5223:exists(flted_12_5286:exists(next_124_1454':exists(prev_122_1446':exists(v_bool_116_1456':exists(p_5284:exists(x':exists(flted_113_218:exists(S1_5314:exists(v_5312:exists(S1_5224:exists(v_5222:S1_5224!=() & 
  S1_5224=union(S1_5289,{v_5287}) & (q_5288=q_5313 & Anon_39=p_5219 & 
  self_5285=x' & v_node_125_1455'=p_5284 & x=p_5284 & res=p_5284 & 
  tmp_219'=p_5284 & v_5312=v_5287 & S1_5289=S1_5314 & 
  flted_12_5221=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1446' & self_5220=p_5284 & q_5223=x' & 1+
  flted_12_5286=flted_113_218 & next_124_1454'=null & prev_122_1446'=null & 
  flted_113_218<=-2 & v_bool_116_1456'<=0 & p_5284!=null & x'!=null | 
  q_5288=q_5313 & Anon_39=p_5219 & self_5285=x' & v_node_125_1455'=p_5284 & 
  x=p_5284 & res=p_5284 & tmp_219'=p_5284 & v_5312=v_5287 & 
  S1_5289=S1_5314 & flted_12_5221=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1446' & self_5220=p_5284 & q_5223=x' & 1+
  flted_12_5286=flted_113_218 & next_124_1454'=null & prev_122_1446'=null & 
  v_bool_116_1456'<=0 & p_5284!=null & x'!=null & 1<=flted_113_218) & 
  S1!=() & S2=union(S1_5314,{v_5312}) & S1=union(S1_5224,
  {v_5222}))))))))))))))))))))))))))))) --> PF(S1,S2)]
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
                              EXISTS(v_5498,n_5499,Anon_5500,q_5501,
                              Anon_5502,
                              S1_5503: x'::node<v_5498,Anon_5500,q_5501>@M[Orig][] * 
                              q_5501::dll<Anon_5502,n_5499,S1_5503>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S1_5503][x'!=null][n=n_5499 & 0<=n]
                               [v=v_5498]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> PUF(S1,S),
 (exists(q_5425:exists(q_5443:exists(v:exists(v_220:exists(n:exists(Anon_38:exists(p_5421:exists(Anon_37:exists(Anon_36:exists(self_5422:exists(q:exists(x':exists(flted_12_5423:exists(v_bool_97_1477':exists(x:exists(tmp_222':exists(n_221:exists(S1_5426:exists(v_5424:exists(S1_5444:exists(v_5442:(q_5425=q_5443 & 
  v=v_220 & n=n_221 & v_5442=v_5424 & S1_5426=S1_5444 & Anon_38=Anon_36 & 
  p_5421=Anon_36 & Anon_37=Anon_36 & self_5422=x & q=x & x'=tmp_222' & 1+
  flted_12_5423=n_221 & n_221<=-1 & v_bool_97_1477'<=0 & x!=null & 
  tmp_222'!=null | q_5425=q_5443 & v=v_220 & n=n_221 & v_5442=v_5424 & 
  S1_5426=S1_5444 & Anon_38=Anon_36 & p_5421=Anon_36 & Anon_37=Anon_36 & 
  self_5422=x & q=x & x'=tmp_222' & 1+flted_12_5423=n_221 & 
  v_bool_97_1477'<=0 & x!=null & tmp_222'!=null & 1<=n_221) & S!=() & 
  S=union(S1_5426,{v_5424}) & S1=union(S1_5444,
  {v_5442}))))))))))))))))))))))) --> PUF(S1,S)]
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
                              EXISTS(Anon_5509,n_5510,
                              S2_5511: x::dll<Anon_5509,n_5510,S2_5511>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([n=n_5510 & 0<=n][S1=S2_5511][res=x]
                               [Anon_5509=Anon_41]))&
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
                              EXISTS(v_6016,y_6017,j_6018,Anon_6020,
                              S2_6021: y::dll<Anon_6020,j_6018,S2_6021>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S2_6021][x!=null][j=j_6018 & 0<=j]
                               [y=y_6017][v=v_6016][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S) --> SN(S,S2),
 (S=S2 & S2=) --> SN(S,S2),
 (exists(q_5942:exists(q_5958:exists(Anon_50:exists(Anon_46:exists(x_5891:exists(x':exists(self_5939:exists(p_5938:exists(Anon_49:exists(j:exists(v:exists(v_206:exists(y_207:exists(x:exists(flted_12_5940:exists(v_bool_224_1343':exists(y:exists(Anon_51:exists(Anon_47:exists(j_208:exists(S1_5943:exists(v_5941:exists(S1_5959:exists(v_5957:(q_5942=q_5958 & 
  Anon_50=Anon_46 & x_5891=Anon_51 & x'=Anon_51 & self_5939=y & 
  p_5938=Anon_49 & v_5957=v_5941 & S1_5943=S1_5959 & j=j_208 & v=v_206 & 
  y_207=y & x=Anon_51 & 1+flted_12_5940=j_208 & j_208<=-1 & 
  v_bool_224_1343'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 | 
  q_5942=q_5958 & Anon_50=Anon_46 & x_5891=Anon_51 & x'=Anon_51 & 
  self_5939=y & p_5938=Anon_49 & v_5957=v_5941 & S1_5943=S1_5959 & j=j_208 & 
  v=v_206 & y_207=y & x=Anon_51 & 1+flted_12_5940=j_208 & 
  v_bool_224_1343'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 & 1<=j_208) & 
  S!=() & S=union(S1_5943,{v_5941}) & S2=union(S1_5959,
  {v_5957})))))))))))))))))))))))))) --> SN(S,S2)]
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
                              EXISTS(p_6858,Anon_6859,n2_6860,n1_6861,
                              S1_6862,
                              S2_6863: x'::dll<p_6858,n1_6861,S1_6862>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_6859,n2_6860,S2_6863>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_6862!=() & S2_6863!=() & union(S1_6862,
                                 S2_6863)=S]
                               [null!=res][null!=x'][p=p_6858]
                               [a=n1_6861 & 0!=n1_6861 & 0<=n & n=n1_6861+
                                 n2_6860 & 0!=n2_6860]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_6652:exists(v_6650:exists(S1_6747:exists(v_6745:S1_6652!=() & 
  S1_6747= & v_6650=v_6745 & S2=S1_6652 & S=union(S1_6652,{v_6650}) & 
  S!=() & S1=union(S1_6747,{v_6745})))))) --> SPLIT(S,S1,S2),
 (exists(S1_6791:exists(v_6789:exists(S1_6701:exists(v_6699:S1_6701!=() & 
  S2_6786!=() & S1_6785!=() & v_6789=v_6699 & S1_6701=S_6704 & 
  S1_6785=S1_6791 & S2_6786=S2 & SPLIT(S_6704,S1_6785,S2_6786) & S!=() & 
  S1=union(S1_6791,{v_6789}) & S=union(S1_6701,
  {v_6699})))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(Anon_6875,m_6876,S3_6877,Anon_6878,
                              n_6879,
                              S4_6880: x'::dll<Anon_6875,m_6876,S3_6877>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                              y'::dll<Anon_6878,n_6879,S4_6880>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([m=m_6876 & 0<=m][n=n_6879 & 0<=n][S1=S4_6880]
                               [S2=S3_6877][y=x'][x=y'][Anon_6875=Anon_31]
                               [Anon_6878=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (543,6)  (239,13)  (239,4)  (342,4)  (342,11)  (352,6)  (352,13)  (351,6)  (351,6)  (349,6)  (349,13)  (348,8)  (347,27)  (347,14)  (347,9)  (346,10)  (346,4)  (345,8)  (345,12)  (345,4)  (345,4) )

Total verification time: 10.62 second(s)
	Time spent in main process: 0.87 second(s)
	Time spent in child processes: 9.75 second(s)
