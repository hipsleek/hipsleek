/usr/local/bin/mona

Processing file "dll_msb.ss"
Parsing dll_msb.ss ...
Parsing ../../../prelude.ss ...
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
                              EXISTS(q_2043,t_2044,
                              S_2045: x::dll<q_2043,t_2044,S_2045>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([union(S1,S2)=S_2045][q=q_2043]
                               [t_2044=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1935:exists(v_1780:exists(v_1933:exists(S1_1782:S1!=() & S2= & 
  S=union(S1_1935,{v_1933}) & S1=union(S1_1782,{v_1780}) & S1_1935=S2 & 
  v_1780=v_1933 & S1_1782=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1779:exists(m:exists(p_1777:exists(q_215:exists(q:exists(self_1840:exists(p_1839:exists(p:exists(v_1893:exists(S1_1895:exists(n:exists(q_1843:exists(q_1894:exists(q_1880:exists(x:exists(flted_12_1841:exists(q_1781:exists(y:exists(self_1778:exists(v_bool_184_1410':exists(v_bool_182_1415':exists(t:exists(S1_1881:exists(v_1879:exists(S1_1782:exists(v_1780:exists(S1_1844:exists(v_1842:S1_1881=union(S1_1895,
  {v_1893}) & S1_1782= & (flted_12_1779=0 & m=1 & p_1777=q & q_215=q & 
  self_1840=y & p_1839=p & v_1879=v_1780 & v_1893=v_1842 & S1_1844=S1_1895 & 
  1+n=t & q_1843=q_1894 & q_1880=y & x=self_1778 & 2+flted_12_1841=t & 
  q_1781=null & t<=0 & y!=null & self_1778!=null & 1<=v_bool_184_1410' & 
  1<=v_bool_182_1415' | flted_12_1779=0 & m=1 & p_1777=q & q_215=q & 
  self_1840=y & p_1839=p & v_1879=v_1780 & v_1893=v_1842 & S1_1844=S1_1895 & 
  1+n=t & q_1843=q_1894 & q_1880=y & x=self_1778 & 2+flted_12_1841=t & 
  q_1781=null & y!=null & self_1778!=null & 1<=v_bool_184_1410' & 
  1<=v_bool_182_1415' & 2<=t) & S2!=() & S=union(S1_1881,{v_1879}) & 
  S1=union(S1_1782,{v_1780}) & S2=union(S1_1844,{v_1842}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1782:exists(v_1780:exists(S1_1935:exists(v_1933:S1_1782= & 
  v_1780=v_1933 & S2=S1_1935 & S1=union(S1_1782,{v_1780}) & S=union(S1_1935,
  {v_1933}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1965:exists(v_1963:exists(S1_1782:exists(v_1780:S_1962!=() & 
  S1_1782!=() & S1_1782=S1_1853 & v_1780=v_1963 & S_1962=S1_1965 & 
  S2_1856=S2 & APP2(S_1962,S1_1853,S2_1856) & S1!=() & S=union(S1_1965,
  {v_1963}) & S1=union(S1_1782,{v_1780})))))) --> APP2(S,S1,S2)]
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
                              
                              EXISTS(n_2287,S4_2288: true&(
                              ([S4_2288=][null=x'][0=n_2287][0=n][0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(S_2289: x'::dll<Anon_35,n_224,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                 (
                                 ([S4=S_2289 & 
                                    662::forall(_x:_x <notin> S_2289  | 
                                    _x=v) & S_2289!=()]
                                  [x'!=null][n_224=n & 1<=n_224]
                                  [Anon_2276_2283_2284=Anon_35][0<=m]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
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
                              or EXISTS(Anon_3235,Anon_3236,
                                 m_3237: res::node<m_3237,Anon_3235,Anon_3236>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_3237 & m_3237 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_3142:exists(Anon_75:exists(Anon_76:exists(Anon_77:exists(q_3146:exists(self_3143:exists(flted_12_3144:exists(v_bool_518_827':exists(v:exists(v_node_522_820':exists(v_bool_521_826':exists(n:exists(S1_3147:exists(v_3145:(x=v_node_522_820' & 
  res=v_node_522_820' & p_3142=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3146 & 
  m=v_3145 & self_3143=v_node_522_820' & 1+flted_12_3144=n & 
  v_bool_518_827'<=0 & (1+v)<=v_3145 & n<=-1 & v_node_522_820'!=null & 
  1<=v_bool_521_826' | x=v_node_522_820' & res=v_node_522_820' & 
  p_3142=Anon_76 & Anon_75=Anon_76 & Anon_77=q_3146 & m=v_3145 & 
  self_3143=v_node_522_820' & 1+flted_12_3144=n & v_bool_518_827'<=0 & (1+
  v)<=v_3145 & v_node_522_820'!=null & 1<=v_bool_521_826' & 1<=n) & S!=() & 
  S=union(S1_3147,{v_3145})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_3147:exists(v_3145:v_3145<=v & S1_3147=S_3173 & 
  m_3211=m & (1+v)<=m & FGE(S_3173,m_3211) & S=union(S1_3147,{v_3145}) & 
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
                              EXISTS(flted_209_3344,flted_209_3345,Anon_3346,
                              Anon_3347,S1_3348,
                              S2_3349: x'::dll<Anon_3346,flted_209_3345,S1_3348>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_3347,flted_209_3344,S2_3349>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S1_3348!=() & union(S1_3348,S2_3349)=S]
                               [null!=x'][1+flted_209_3344=n & 0<=n]
                               [1=flted_209_3345]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_209_212:exists(q_3292:exists(tmp_213':exists(res:exists(q_3272:exists(v_node_214_1371':exists(Anon_43:exists(p_3268:exists(self_3269:exists(x':exists(n:exists(next_213_3290:exists(prev_213_1369':exists(x:exists(flted_209_211:exists(next_212_1366':exists(Anon_44:exists(Anon_45:exists(flted_12_3270:exists(S1_3273:exists(v_3271:exists(S1_3293:exists(v_3291:S1_3293= & 
  (flted_209_212=1 & q_3292=next_212_1366' & tmp_213'=v_node_214_1371' & 
  res=v_node_214_1371' & q_3272=v_node_214_1371' & Anon_43=p_3268 & 
  self_3269=Anon_45 & x'=Anon_45 & -1+n=flted_12_3270 & v_3291=v_3271 & 
  S1_3273=S2 & next_213_3290=next_212_1366' & prev_213_1369'=Anon_44 & 
  x=Anon_45 & flted_209_211=flted_12_3270 & next_212_1366'=null & 
  Anon_44=null & flted_12_3270<=-2 & Anon_45!=null | flted_209_212=1 & 
  q_3292=next_212_1366' & tmp_213'=v_node_214_1371' & res=v_node_214_1371' & 
  q_3272=v_node_214_1371' & Anon_43=p_3268 & self_3269=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_3270 & v_3291=v_3271 & S1_3273=S2 & 
  next_213_3290=next_212_1366' & prev_213_1369'=Anon_44 & x=Anon_45 & 
  flted_209_211=flted_12_3270 & next_212_1366'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_3270) & S=union(S1_3273,{v_3271}) & 
  S1=union(S1_3293,{v_3291}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
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
                              EXISTS(flted_255_3444,Anon_3445,
                              S2_3446: res::dll<Anon_3445,flted_255_3444,S2_3446>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([2+flted_255_3444=n & 0<=n]
                               [S2_3446<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3421:exists(S1_3423:exists(S1_3380:exists(v_3378:S1_3380=union(S1_3423,
  {v_3421}) & S1_3380!=() & S2=S1_3423 & S!=() & S=union(S1_3380,
  {v_3378})))))) --> GNN(S,S2)]
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
                              EXISTS(p_3611,m_3612,
                              S1_3613: x::dll<p_3611,m_3612,S1_3613>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_3613!=() & S1_3613=union(S,{a})][null!=x]
                               [p=p_3611][-1+m_3612=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3539:exists(v_3537:exists(S1_3525:exists(v_3523:exists(S1_3478:exists(v_3476:S1_3539= & 
  S1_3525=union(S1_3539,{v_3537}) & S1_3478= & v_3476=v_3523 & v_3537=a & 
  S1=union(S1_3525,{v_3523}) & S=union(S1_3478,{v_3476}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3566:exists(v_3564:exists(S1_3478:exists(v_3476:S1_3478!=() & 
  S1_3563!=() & v_3564=v_3476 & S1_3478=S_3506 & S1_3563=S1_3566 & 
  INSERT(S_3506,S1_3563,a) & S!=() & S1=union(S1_3566,{v_3564}) & 
  S=union(S1_3478,{v_3476})))))) --> INSERT(S,S1,a)]
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
                              EXISTS(p_5174,n_5175,
                              S2_5176: x::dll<p_5174,n_5175,S2_5176>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (([S1=S2_5176][n=n_5175 & 0<=n][p=p_5174]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_5134:exists(v_5132:exists(S1_5108:exists(v_5106:v_5132=v_5106 & 
  S1_5108=S1_5114 & S2_5131=S1_5134 & TRAV(S1_5114,S2_5131) & S1!=() & 
  S2=union(S1_5134,{v_5132}) & S1=union(S1_5108,
  {v_5106})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_113_5368,Anon_5369,
                              S2_5370: x'::dll<Anon_5369,flted_113_5368,S2_5370>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([1+flted_113_5368=m & 0<=m]
                               [S2_5370<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5209:exists(v_5207:S1_5209= & S2= & S1=union(S1_5209,{v_5207}) & 
  S1!=()))) --> PF(S1,S2),
 (exists(q_5273:exists(q_5298:exists(Anon_39:exists(p_5204:exists(self_5270:exists(v_node_125_1455':exists(x:exists(res:exists(tmp_219':exists(v_5272:exists(S1_5274:exists(flted_12_5206:exists(m:exists(Anon_40:exists(self_5205:exists(q_5208:exists(flted_12_5271:exists(next_124_1454':exists(prev_122_1446':exists(v_bool_116_1456':exists(p_5269:exists(x':exists(flted_113_218:exists(S1_5299:exists(v_5297:exists(S1_5209:exists(v_5207:S1_5209!=() & 
  S1_5209=union(S1_5274,{v_5272}) & (q_5273=q_5298 & Anon_39=p_5204 & 
  self_5270=x' & v_node_125_1455'=p_5269 & x=p_5269 & res=p_5269 & 
  tmp_219'=p_5269 & v_5297=v_5272 & S1_5274=S1_5299 & 
  flted_12_5206=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1446' & self_5205=p_5269 & q_5208=x' & 1+
  flted_12_5271=flted_113_218 & next_124_1454'=null & prev_122_1446'=null & 
  flted_113_218<=-2 & v_bool_116_1456'<=0 & p_5269!=null & x'!=null | 
  q_5273=q_5298 & Anon_39=p_5204 & self_5270=x' & v_node_125_1455'=p_5269 & 
  x=p_5269 & res=p_5269 & tmp_219'=p_5269 & v_5297=v_5272 & 
  S1_5274=S1_5299 & flted_12_5206=flted_113_218 & -1+m=flted_113_218 & 
  Anon_40=prev_122_1446' & self_5205=p_5269 & q_5208=x' & 1+
  flted_12_5271=flted_113_218 & next_124_1454'=null & prev_122_1446'=null & 
  v_bool_116_1456'<=0 & p_5269!=null & x'!=null & 1<=flted_113_218) & 
  S1!=() & S2=union(S1_5299,{v_5297}) & S1=union(S1_5209,
  {v_5207}))))))))))))))))))))))))))))) --> PF(S1,S2)]
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
                              EXISTS(v_5483,n_5484,Anon_5485,q_5486,
                              Anon_5487,
                              S1_5488: x'::node<v_5483,Anon_5485,q_5486>@M[Orig][] * 
                              q_5486::dll<Anon_5487,n_5484,S1_5488>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S1_5488][x'!=null][n=n_5484 & 0<=n]
                               [v=v_5483]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> PUF(S1,S),
 (exists(q_5410:exists(q_5428:exists(v:exists(v_220:exists(n:exists(Anon_38:exists(p_5406:exists(Anon_37:exists(Anon_36:exists(self_5407:exists(q:exists(x':exists(flted_12_5408:exists(v_bool_97_1477':exists(x:exists(tmp_222':exists(n_221:exists(S1_5411:exists(v_5409:exists(S1_5429:exists(v_5427:(q_5410=q_5428 & 
  v=v_220 & n=n_221 & v_5427=v_5409 & S1_5411=S1_5429 & Anon_38=Anon_36 & 
  p_5406=Anon_36 & Anon_37=Anon_36 & self_5407=x & q=x & x'=tmp_222' & 1+
  flted_12_5408=n_221 & n_221<=-1 & v_bool_97_1477'<=0 & x!=null & 
  tmp_222'!=null | q_5410=q_5428 & v=v_220 & n=n_221 & v_5427=v_5409 & 
  S1_5411=S1_5429 & Anon_38=Anon_36 & p_5406=Anon_36 & Anon_37=Anon_36 & 
  self_5407=x & q=x & x'=tmp_222' & 1+flted_12_5408=n_221 & 
  v_bool_97_1477'<=0 & x!=null & tmp_222'!=null & 1<=n_221) & S!=() & 
  S=union(S1_5411,{v_5409}) & S1=union(S1_5429,
  {v_5427}))))))))))))))))))))))) --> PUF(S1,S)]
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
                              EXISTS(Anon_5494,n_5495,
                              S2_5496: x::dll<Anon_5494,n_5495,S2_5496>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([n=n_5495 & 0<=n][S1=S2_5496][res=x]
                               [Anon_5494=Anon_41]))&
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
                              EXISTS(v_6001,y_6002,j_6003,Anon_6005,
                              S2_6006: y::dll<Anon_6005,j_6003,S2_6006>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S2_6006][x!=null][j=j_6003 & 0<=j]
                               [y=y_6002][v=v_6001][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S) --> SN(S,S2),
 (S=S2 & S2=) --> SN(S,S2),
 (exists(q_5927:exists(q_5943:exists(Anon_50:exists(Anon_46:exists(x_5876:exists(x':exists(self_5924:exists(p_5923:exists(Anon_49:exists(j:exists(v:exists(v_206:exists(y_207:exists(x:exists(flted_12_5925:exists(v_bool_224_1343':exists(y:exists(Anon_51:exists(Anon_47:exists(j_208:exists(S1_5928:exists(v_5926:exists(S1_5944:exists(v_5942:(q_5927=q_5943 & 
  Anon_50=Anon_46 & x_5876=Anon_51 & x'=Anon_51 & self_5924=y & 
  p_5923=Anon_49 & v_5942=v_5926 & S1_5928=S1_5944 & j=j_208 & v=v_206 & 
  y_207=y & x=Anon_51 & 1+flted_12_5925=j_208 & j_208<=-1 & 
  v_bool_224_1343'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 | 
  q_5927=q_5943 & Anon_50=Anon_46 & x_5876=Anon_51 & x'=Anon_51 & 
  self_5924=y & p_5923=Anon_49 & v_5942=v_5926 & S1_5928=S1_5944 & j=j_208 & 
  v=v_206 & y_207=y & x=Anon_51 & 1+flted_12_5925=j_208 & 
  v_bool_224_1343'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 & 1<=j_208) & 
  S!=() & S=union(S1_5928,{v_5926}) & S2=union(S1_5944,
  {v_5942})))))))))))))))))))))))))) --> SN(S,S2)]
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
                              EXISTS(p_6843,Anon_6844,n2_6845,n1_6846,
                              S1_6847,
                              S2_6848: x'::dll<p_6843,n1_6846,S1_6847>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_6844,n2_6845,S2_6848>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_6847!=() & S2_6848!=() & union(S1_6847,
                                 S2_6848)=S]
                               [null!=res][null!=x'][p=p_6843]
                               [a=n1_6846 & 0!=n1_6846 & 0<=n & n=n1_6846+
                                 n2_6845 & 0!=n2_6845]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_6637:exists(v_6635:exists(S1_6732:exists(v_6730:S1_6637!=() & 
  S1_6732= & v_6635=v_6730 & S2=S1_6637 & S=union(S1_6637,{v_6635}) & 
  S!=() & S1=union(S1_6732,{v_6730})))))) --> SPLIT(S,S1,S2),
 (exists(S1_6776:exists(v_6774:exists(S1_6686:exists(v_6684:S1_6686!=() & 
  S2_6771!=() & S1_6770!=() & v_6774=v_6684 & S1_6686=S_6689 & 
  S1_6770=S1_6776 & S2_6771=S2 & SPLIT(S_6689,S1_6770,S2_6771) & S!=() & 
  S1=union(S1_6776,{v_6774}) & S=union(S1_6686,
  {v_6684})))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(Anon_6860,m_6861,S3_6862,Anon_6863,
                              n_6864,
                              S4_6865: x'::dll<Anon_6860,m_6861,S3_6862>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                              y'::dll<Anon_6863,n_6864,S4_6865>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([m=m_6861 & 0<=m][n=n_6864 & 0<=n][S1=S4_6865]
                               [S2=S3_6862][y=x'][x=y'][Anon_6860=Anon_31]
                               [Anon_6863=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (543,6)  (239,13)  (239,4)  (342,4)  (342,11)  (352,6)  (352,13)  (351,6)  (351,6)  (349,6)  (349,13)  (348,8)  (347,27)  (347,14)  (347,9)  (346,10)  (346,4)  (345,8)  (345,12)  (345,4)  (345,4) )

Total verification time: 14.14 second(s)
	Time spent in main process: 4.28 second(s)
	Time spent in child processes: 9.86 second(s)
