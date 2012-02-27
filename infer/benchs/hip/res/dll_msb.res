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
!!! POST:  S1<subset> S  & S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                    ([0!=m][null!=x][S1!=()][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(q_211,t,
                                S: x::dll<q_211,t,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([t=m+n][APP2(S,S1,S2)][q=q_211]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(q_2031,t_2032,
                              S_2033: x::dll<q_2031,t_2032,S_2033>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([q=q_2031][t_2032=m+n & 0<=m & 0<=n]
                               [S1<subset> S_2033  & S2<subset> S_2033 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1926:exists(v_1771:exists(v_1924:exists(S1_1773:S1!=() & S2= & 
  S=union(S1_1926,{v_1924}) & S1=union(S1_1773,{v_1771}) & S1_1926=S2 & 
  v_1771=v_1924 & S1_1773=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1770:exists(m:exists(p_1768:exists(q_211:exists(q:exists(self_1831:exists(p_1830:exists(p:exists(v_1884:exists(S1_1886:exists(n:exists(q_1834:exists(q_1885:exists(q_1871:exists(x:exists(flted_12_1832:exists(q_1772:exists(y:exists(self_1769:exists(v_bool_184_1401':exists(v_bool_182_1406':exists(t:exists(S1_1872:exists(v_1870:exists(S1_1773:exists(v_1771:exists(S1_1835:exists(v_1833:S1_1872=union(S1_1886,
  {v_1884}) & S1_1773= & (flted_12_1770=0 & m=1 & p_1768=q & q_211=q & 
  self_1831=y & p_1830=p & v_1870=v_1771 & v_1884=v_1833 & S1_1835=S1_1886 & 
  1+n=t & q_1834=q_1885 & q_1871=y & x=self_1769 & 2+flted_12_1832=t & 
  q_1772=null & t<=0 & y!=null & self_1769!=null & 1<=v_bool_184_1401' & 
  1<=v_bool_182_1406' | flted_12_1770=0 & m=1 & p_1768=q & q_211=q & 
  self_1831=y & p_1830=p & v_1870=v_1771 & v_1884=v_1833 & S1_1835=S1_1886 & 
  1+n=t & q_1834=q_1885 & q_1871=y & x=self_1769 & 2+flted_12_1832=t & 
  q_1772=null & y!=null & self_1769!=null & 1<=v_bool_184_1401' & 
  1<=v_bool_182_1406' & 2<=t) & S2!=() & S=union(S1_1872,{v_1870}) & 
  S1=union(S1_1773,{v_1771}) & S2=union(S1_1835,{v_1833}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1773:exists(v_1771:exists(S1_1926:exists(v_1924:S1_1773= & 
  v_1771=v_1924 & S2=S1_1926 & S1=union(S1_1773,{v_1771}) & S=union(S1_1926,
  {v_1924}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1956:exists(v_1954:exists(S1_1773:exists(v_1771:S_1953!=() & 
  S1_1773!=() & S1_1773=S1_1844 & v_1771=v_1954 & S_1953=S1_1956 & 
  S2_1847=S2 & APP2(S_1953,S1_1844,S2_1847) & S1!=() & S=union(S1_1956,
  {v_1954}) & S1=union(S1_1773,{v_1771})))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CL(S,v)
!!! POST:  S={v} & forall(_x:_x <notin> S  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&(([true]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 68::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 69::
                                                         EXISTS(n_189,
                                                         Anon_65,
                                                         S: res::dll<Anon_65,n_189,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                                         (
                                                         ([CL(S,v)][n=n_189]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 70::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(())&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 68::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 69::
                                                       EXISTS(n_2240,
                                                       Anon_2241,
                                                       S_2242: res::dll<Anon_2241,n_2240,S_2242>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                                       (
                                                       ([forall(_x:_x <notin> S_2242
                                                           | _x=v) & 
                                                          S_2242={v}]
                                                        [n=n_2240 & 1<=n]))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 70::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_2166:exists(v_2164:S1_2166= & v_2164=v & S=union(S1_2166,
  {v_2164})))) --> CL(S,v),
 (exists(S1_2200:exists(v_2198:exists(S1_2155:exists(v_2153:exists(S1_2186:exists(v_2184:S1_2155=S1_2200 & 
  v_2198=v_2153 & S1_2186=union(S1_2200,{v_2198}) & S_2108=union(S1_2155,
  {v_2153}) & S_2108!=() & v=v_2184 & CL(S_2108,v) & S=union(S1_2186,
  {v_2184})))))))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... Timeout when checking #simplify  Restarting Omega after ... 37 invocations Stop Omega... 37 invocations Starting Omega...oc

!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_34; m; 
                    S3](ex)x::dll<Anon_34,m,S3>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_220,Anon_35,
                                S4: x'::dll<Anon_35,n_220,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([n=n_220]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_34; m; 
                  S3](ex)x::dll<Anon_34,m,S3>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              EXISTS(n_2272,S4_2273: true&(
                              ([S4_2273=][null=x'][0=n_2272][0=n][0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(S_2274: x'::dll<Anon_35,n_220,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                 (
                                 ([S4=S_2274 & 
                                    658::forall(_x:_x <notin> S_2274  | 
                                    _x=v) & S_2274!=() & S_2274={v}]
                                  [x'!=null][n_220=n & 1<=n_220]
                                  [Anon_2261_2268_2269=Anon_35][0<=m]))&
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
              EBase exists (Expl)(Impl)[Anon_74; n; 
                    S](ex)x::dll<Anon_74,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 127::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_75,Anon_76,
                                   m: res::node<m,Anon_75,Anon_76>@M[Orig][]&
                                   (([FGE(S,m) & (1+v)<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_74; n; 
                  S](ex)x::dll<Anon_74,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 127::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_3220,Anon_3221,
                                 m_3222: res::node<m_3222,Anon_3220,Anon_3221>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_3222 & m_3222 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_3127:exists(Anon_74:exists(Anon_75:exists(Anon_76:exists(q_3131:exists(self_3128:exists(flted_12_3129:exists(v_bool_518_825':exists(v:exists(v_node_522_818':exists(v_bool_521_824':exists(n:exists(S1_3132:exists(v_3130:(x=v_node_522_818' & 
  res=v_node_522_818' & p_3127=Anon_75 & Anon_74=Anon_75 & Anon_76=q_3131 & 
  m=v_3130 & self_3128=v_node_522_818' & 1+flted_12_3129=n & 
  v_bool_518_825'<=0 & (1+v)<=v_3130 & n<=-1 & v_node_522_818'!=null & 
  1<=v_bool_521_824' | x=v_node_522_818' & res=v_node_522_818' & 
  p_3127=Anon_75 & Anon_74=Anon_75 & Anon_76=q_3131 & m=v_3130 & 
  self_3128=v_node_522_818' & 1+flted_12_3129=n & v_bool_518_825'<=0 & (1+
  v)<=v_3130 & v_node_522_818'!=null & 1<=v_bool_521_824' & 1<=n) & S!=() & 
  S=union(S1_3132,{v_3130})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_3132:exists(v_3130:v_3130<=v & S1_3132=S_3158 & 
  m_3196=m & (1+v)<=m & FGE(S_3158,m_3196) & S=union(S1_3132,{v_3130}) & 
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
                                EXISTS(flted_209_207,flted_209_208,Anon_44,
                                Anon_45,S1,
                                S2: x'::dll<Anon_44,flted_209_208,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                                res::dll<Anon_45,flted_209_207,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (
                                ([1=flted_209_208][1+flted_209_207=n]
                                 [S1!=() & GN(S,S1,S2)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_43; n; 
                  S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              EXISTS(flted_209_3329,flted_209_3330,Anon_3331,
                              Anon_3332,S1_3333,
                              S2_3334: x'::dll<Anon_3331,flted_209_3330,S1_3333>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_3332,flted_209_3329,S2_3334>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S1_3333!=() & union(S1_3333,S2_3334)=S]
                               [null!=x'][1+flted_209_3329=n & 0<=n]
                               [1=flted_209_3330]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_209_208:exists(q_3277:exists(tmp_209':exists(res:exists(q_3257:exists(v_node_214_1362':exists(Anon_43:exists(p_3253:exists(self_3254:exists(x':exists(n:exists(next_213_3275:exists(prev_213_1360':exists(x:exists(flted_209_207:exists(next_212_1357':exists(Anon_44:exists(Anon_45:exists(flted_12_3255:exists(S1_3258:exists(v_3256:exists(S1_3278:exists(v_3276:S1_3278= & 
  (flted_209_208=1 & q_3277=next_212_1357' & tmp_209'=v_node_214_1362' & 
  res=v_node_214_1362' & q_3257=v_node_214_1362' & Anon_43=p_3253 & 
  self_3254=Anon_45 & x'=Anon_45 & -1+n=flted_12_3255 & v_3276=v_3256 & 
  S1_3258=S2 & next_213_3275=next_212_1357' & prev_213_1360'=Anon_44 & 
  x=Anon_45 & flted_209_207=flted_12_3255 & next_212_1357'=null & 
  Anon_44=null & flted_12_3255<=-2 & Anon_45!=null | flted_209_208=1 & 
  q_3277=next_212_1357' & tmp_209'=v_node_214_1362' & res=v_node_214_1362' & 
  q_3257=v_node_214_1362' & Anon_43=p_3253 & self_3254=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_3255 & v_3276=v_3256 & S1_3258=S2 & 
  next_213_3275=next_212_1357' & prev_213_1360'=Anon_44 & x=Anon_45 & 
  flted_209_207=flted_12_3255 & next_212_1357'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_3255) & S=union(S1_3258,{v_3256}) & 
  S1=union(S1_3278,{v_3276}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[Anon_61; n; 
                    S](ex)x::dll<Anon_61,n,S>@M[Orig][LHSCase]@ rem br[{525}]&
                    (([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(flted_255_199,Anon_62,
                                S2: res::dll<Anon_62,flted_255_199,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([2+flted_255_199=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_61; n; 
                  S](ex)x::dll<Anon_61,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              EXISTS(flted_255_3429,Anon_3430,
                              S2_3431: res::dll<Anon_3430,flted_255_3429,S2_3431>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([2+flted_255_3429=n & 0<=n]
                               [S2_3431<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3406:exists(S1_3408:exists(S1_3365:exists(v_3363:S1_3365=union(S1_3408,
  {v_3406}) & S1_3365!=() & S2=S1_3408 & S!=() & S=union(S1_3365,
  {v_3363})))))) --> GNN(S,S2)]
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
                                EXISTS(p_197,m,
                                S1: x::dll<p_197,m,S1>@M[Orig][LHSCase]@ rem br[{525}]&
                                (
                                ([-1+m=n][S1!=() & INSERT(S,S1,a)][p=p_197]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(p_3596,m_3597,
                              S1_3598: x::dll<p_3596,m_3597,S1_3598>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_3598!=() & S1_3598=union(S,{a})][null!=x]
                               [p=p_3596][-1+m_3597=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3524:exists(v_3522:exists(S1_3510:exists(v_3508:exists(S1_3463:exists(v_3461:S1_3524= & 
  S1_3510=union(S1_3524,{v_3522}) & S1_3463= & v_3461=v_3508 & v_3522=a & 
  S1=union(S1_3510,{v_3508}) & S=union(S1_3463,{v_3461}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3551:exists(v_3549:exists(S1_3463:exists(v_3461:S1_3463!=() & 
  S1_3548!=() & v_3549=v_3461 & S1_3463=S_3491 & S1_3548=S1_3551 & 
  INSERT(S_3491,S1_3548,a) & S!=() & S1=union(S1_3551,{v_3549}) & 
  S=union(S1_3463,{v_3461})))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CPY(S,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 95::
                                EXISTS(p_168,n_169,S_170,n_171,Anon_71,
                                S2: x::dll<p_168,n_169,S_170>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                                res::dll<Anon_71,n_171,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (
                                ([p=p_168][S=S_170 & CPY(S,S2)]
                                 [n=n_171 & n=n_169]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 95::
                              EXISTS(p_3936,n_3937,S_3938,n_3939,Anon_3940,
                              S2_3941: x::dll<p_3936,n_3937,S_3938>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                              res::dll<Anon_3940,n_3939,S2_3941>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([n=n_3937 & n=n_3939 & 0<=n][S=S_3938]
                               [p=p_3936]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3857:exists(v_3855:exists(v_3632:exists(S_170:exists(S1_3831:exists(v_3829:exists(S1_3634:S!=() & 
  S2=union(S1_3857,{v_3855}) & S=union(S1_3634,{v_3632}) & 
  CPY(S_3640,S2_3667) & S1_3857=S2_3667 & v_3829=v_3632 & v_3855=v_3632 & 
  S_3640=S1_3634 & S1_3831=S1_3634 & S_170=union(S1_3831,{v_3829}) & 
  S2_3667= & S1_3634=)))))))) --> CPY(S,S2),
 (exists(S1_3857:exists(v_3855:exists(v_3632:exists(S_170:exists(S1_3831:exists(v_3829:exists(S1_3634:S!=() & 
  S2=union(S1_3857,{v_3855}) & S=union(S1_3634,{v_3632}) & 
  CPY(S_3640,S2_3667) & S1_3857=S2_3667 & v_3829=v_3632 & v_3855=v_3632 & 
  S_3640=S1_3634 & S1_3831=S1_3634 & S_170=union(S1_3831,{v_3829}) & 
  S1_3634= & S2_3667=)))))))) --> CPY(S,S2),
 (exists(S1_3883:exists(v_3632:exists(v_3881:exists(S_170:exists(S1_3831:exists(v_3829:exists(S1_3634:S=union(S1_3634,
  {v_3632}) & S2=union(S1_3883,{v_3881}) & S!=() & CPY(S_3640,S2_3667) & 
  S1_3883=S2_3667 & v_3632=v_3829 & v_3881=v_3829 & S1_3634=S_3640 & 
  S1_3831=S_3640 & S_170=union(S1_3831,{v_3829}) & S2_3667= & 
  S1_3634=)))))))) --> CPY(S,S2),
 (exists(S_170:S2= & S_170=S & S_170=)) --> CPY(S,S2),
 (exists(S1_3785:exists(v_3783:exists(S1_3732:exists(v_3730:exists(S_170:exists(S1_3743:exists(v_3741:exists(S1_3771:exists(v_3769:exists(S1_3634:exists(v_3632:S1_3732=S1_3785 & 
  v_3730=v_3783 & S1_3771=union(S1_3785,{v_3783}) & S2_3667!=() & 
  S2_3667=union(S1_3732,{v_3730}) & S1_3634!=() & S_170=union(S1_3743,
  {v_3741}) & S1_3743=S1_3634 & S_3640=S1_3634 & v_3769=v_3741 & 
  v_3632=v_3741 & CPY(S_3640,S2_3667) & S2=union(S1_3771,{v_3769}) & 
  S=union(S1_3634,{v_3632}) & S!=())))))))))))) --> CPY(S,S2),
 (exists(S_170:exists(S1_3831:exists(v_3829:exists(S1_3634:exists(v_3632:exists(S1_3883:exists(v_3881:S1_3634= & 
  S2_3667= & S_170=union(S1_3831,{v_3829}) & S1_3831=S_3640 & 
  S1_3634=S_3640 & v_3881=v_3829 & v_3632=v_3829 & S1_3883=S2_3667 & 
  CPY(S_3640,S2_3667) & S=union(S1_3634,{v_3632}) & S2=union(S1_3883,
  {v_3881}) & S!=())))))))) --> CPY(S,S2),
 (exists(S_170:S_170= & S=S_170 & S2=)) --> CPY(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
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
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; n; 
                    S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 92::
                                EXISTS(p_174,n_175,
                                S2: x::dll<p_174,n_175,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([TRAV(S1,S2)][p=p_174][n=n_175]))&
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
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_39; m; 
                    S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{525}]&
                    (([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(flted_113_214,Anon_40,
                                S2: x'::dll<Anon_40,flted_113_214,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([1+flted_113_214=m][PF(S1,S2)]))&
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
 (exists(q_5273:exists(q_5298:exists(Anon_39:exists(p_5204:exists(self_5270:exists(v_node_125_1446':exists(x:exists(res:exists(tmp_215':exists(v_5272:exists(S1_5274:exists(flted_12_5206:exists(m:exists(Anon_40:exists(self_5205:exists(q_5208:exists(flted_12_5271:exists(next_124_1445':exists(prev_122_1437':exists(v_bool_116_1447':exists(p_5269:exists(x':exists(flted_113_214:exists(S1_5299:exists(v_5297:exists(S1_5209:exists(v_5207:S1_5209!=() & 
  S1_5209=union(S1_5274,{v_5272}) & (q_5273=q_5298 & Anon_39=p_5204 & 
  self_5270=x' & v_node_125_1446'=p_5269 & x=p_5269 & res=p_5269 & 
  tmp_215'=p_5269 & v_5297=v_5272 & S1_5274=S1_5299 & 
  flted_12_5206=flted_113_214 & -1+m=flted_113_214 & 
  Anon_40=prev_122_1437' & self_5205=p_5269 & q_5208=x' & 1+
  flted_12_5271=flted_113_214 & next_124_1445'=null & prev_122_1437'=null & 
  flted_113_214<=-2 & v_bool_116_1447'<=0 & p_5269!=null & x'!=null | 
  q_5273=q_5298 & Anon_39=p_5204 & self_5270=x' & v_node_125_1446'=p_5269 & 
  x=p_5269 & res=p_5269 & tmp_215'=p_5269 & v_5297=v_5272 & 
  S1_5274=S1_5299 & flted_12_5206=flted_113_214 & -1+m=flted_113_214 & 
  Anon_40=prev_122_1437' & self_5205=p_5269 & q_5208=x' & 1+
  flted_12_5271=flted_113_214 & next_124_1445'=null & prev_122_1437'=null & 
  v_bool_116_1447'<=0 & p_5269!=null & x'!=null & 1<=flted_113_214) & 
  S1!=() & S2=union(S1_5299,{v_5297}) & S1=union(S1_5209,
  {v_5207}))))))))))))))))))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(S1,S,v)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_36; n; 
                    S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(v_216,n_217,Anon_37,q,Anon_38,
                                S1: x'::node<v_216,Anon_37,q>@M[Orig][] * 
                                q::dll<Anon_38,n_217,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (
                                ([v=v_216 & PUF(S1,S,v)][n=n_217][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36; n; 
                  S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(v_5482,n_5483,Anon_5484,q_5485,
                              Anon_5486,
                              S1_5487: x'::node<v_5482,Anon_5484,q_5485>@M[Orig][] * 
                              q_5485::dll<Anon_5486,n_5483,S1_5487>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([S=S1_5487][x'!=null][n=n_5483 & 0<=n]
                               [v=v_5482]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_216:v_216=v & S1= & S=)) --> PUF(S1,S,v),
 (exists(q_5410:exists(q_5428:exists(v_216:exists(n:exists(Anon_38:exists(p_5406:exists(Anon_37:exists(Anon_36:exists(self_5407:exists(q:exists(x':exists(flted_12_5408:exists(v_bool_97_1468':exists(x:exists(tmp_218':exists(n_217:exists(S1_5411:exists(v_5409:exists(S1_5429:exists(v_5427:(q_5410=q_5428 & 
  v=v_216 & n=n_217 & v_5427=v_5409 & S1_5411=S1_5429 & Anon_38=Anon_36 & 
  p_5406=Anon_36 & Anon_37=Anon_36 & self_5407=x & q=x & x'=tmp_218' & 1+
  flted_12_5408=n_217 & n_217<=-1 & v_bool_97_1468'<=0 & x!=null & 
  tmp_218'!=null | q_5410=q_5428 & v=v_216 & n=n_217 & v_5427=v_5409 & 
  S1_5411=S1_5429 & Anon_38=Anon_36 & p_5406=Anon_36 & Anon_37=Anon_36 & 
  self_5407=x & q=x & x'=tmp_218' & 1+flted_12_5408=n_217 & 
  v_bool_97_1468'<=0 & x!=null & tmp_218'!=null & 1<=n_217) & S!=() & 
  S=union(S1_5411,{v_5409}) & S1=union(S1_5429,
  {v_5427})))))))))))))))))))))) --> PUF(S1,S,v)]
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
                                EXISTS(n_210,Anon_42,
                                S2: x::dll<Anon_42,n_210,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([n=n_210]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_41; n; 
                  S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              EXISTS(Anon_5493,n_5494,
                              S2_5495: x::dll<Anon_5493,n_5494,S2_5495>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([n=n_5494 & 0<=n][S1=S2_5495][res=x]
                               [Anon_5493=Anon_41]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SN(S,S2,v)
!!! POST:  S<subset> S2  & v <in> S2 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                    Anon_49; j; 
                    S](ex)EXISTS(x_204: x::node<v,Anon_46,t>@M[Orig][] * 
                    t::dll<x_204,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                    y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                    ([x=x_204 & x!=null][0<=Anon_47][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::ref [x]
                                EXISTS(Anon_50,k,
                                S2: x::dll<Anon_50,k,S2>@M[Orig][LHSCase]@ rem br[{525}]&
                                (([-1+k=j][S2!=() & SN(S,S2,v)][null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                  Anon_49; j; S](ex)x::node<v,Anon_46,t>@M[Orig][] * 
                  t::dll<x_204,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                  y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ([x=x_204 & x!=null][0<=Anon_47]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::ref [x]
                              EXISTS(k_6033,S2_6034: true&(
                              ([S<subset> S2_6034  & S2_6034!=() & 
                                 v <in> S2_6034 ]
                               [null!=x][-1+k_6033=j & 0<=j][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5935:exists(v_5933:S1_5935= & v_5933=v & S= & S2=union(S1_5935,
  {v_5933})))) --> SN(S,S2,v),
 (exists(Anon_50:exists(Anon_46:exists(j:exists(p_5922:exists(Anon_49:exists(self_5923:exists(x':exists(v_5967:exists(S1_5969:exists(q_5926:exists(q_5968:exists(q_5954:exists(x:exists(flted_12_5924:exists(v_bool_224_1334':exists(y:exists(x_5875:exists(Anon_47:exists(k:exists(S1_5955:exists(v_5953:exists(S1_5927:exists(v_5925:S1_5955=union(S1_5969,
  {v_5967}) & (Anon_50=Anon_46 & 1+j=k & p_5922=Anon_49 & self_5923=y & 
  x'=x_5875 & v_5953=v & v_5967=v_5925 & S1_5927=S1_5969 & q_5926=q_5968 & 
  q_5954=y & x=x_5875 & 2+flted_12_5924=k & k<=0 & v_bool_224_1334'<=0 & 
  y!=null & x_5875!=null & 0<=Anon_47 | Anon_50=Anon_46 & 1+j=k & 
  p_5922=Anon_49 & self_5923=y & x'=x_5875 & v_5953=v & v_5967=v_5925 & 
  S1_5927=S1_5969 & q_5926=q_5968 & q_5954=y & x=x_5875 & 2+
  flted_12_5924=k & v_bool_224_1334'<=0 & y!=null & x_5875!=null & 
  0<=Anon_47 & 2<=k) & S!=() & S2=union(S1_5955,{v_5953}) & S=union(S1_5927,
  {v_5925}))))))))))))))))))))))))) --> SN(S,S2,v)]
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
                                EXISTS(p_177,Anon_69,n2,n1,S1,
                                S2: x'::dll<p_177,n1,S1>@M[Orig][LHSCase]@ rem br[{525}] * 
                                res::dll<Anon_69,n2,S2>@M[Orig][LHSCase]@ rem br[{525}]&
                                (
                                ([a=n1 & 0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][p=p_177]
                                 [null!=x'][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{525}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 85::ref [x]
                              EXISTS(p_6871,Anon_6872,n2_6873,n1_6874,
                              S1_6875,
                              S2_6876: x'::dll<p_6871,n1_6874,S1_6875>@M[Orig][LHSCase]@ rem br[{525}] * 
                              res::dll<Anon_6872,n2_6873,S2_6876>@M[Orig][LHSCase]@ rem br[{525}]&
                              (
                              ([S1_6875!=() & S2_6876!=() & union(S1_6875,
                                 S2_6876)=S]
                               [null!=res][null!=x'][p=p_6871]
                               [a=n1_6874 & 0!=n1_6874 & 0<=n & n=n1_6874+
                                 n2_6873 & 0!=n2_6873]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_6665:exists(v_6663:exists(S1_6760:exists(v_6758:S1_6665!=() & 
  S1_6760= & v_6663=v_6758 & S2=S1_6665 & S=union(S1_6665,{v_6663}) & 
  S!=() & S1=union(S1_6760,{v_6758})))))) --> SPLIT(S,S1,S2),
 (exists(S1_6804:exists(v_6802:exists(S1_6714:exists(v_6712:S1_6714!=() & 
  S2_6799!=() & S1_6798!=() & v_6802=v_6712 & S1_6714=S_6717 & 
  S1_6798=S1_6804 & S2_6799=S2 & SPLIT(S_6717,S1_6798,S2_6799) & S!=() & 
  S1=union(S1_6804,{v_6802}) & S=union(S1_6714,
  {v_6712})))))) --> SPLIT(S,S1,S2)]
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
                                EXISTS(m_221,n_222,Anon_32,S3,Anon_33,
                                S4: x'::dll<Anon_32,m_221,S3>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                                y'::dll<Anon_33,n_222,S4>@M[Orig][LHSCase]@ rem br[{526,525}]&
                                (([m=m_221][n=n_222]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                  S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                  y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{526,525}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(Anon_6888,m_6889,S3_6890,Anon_6891,
                              n_6892,
                              S4_6893: x'::dll<Anon_6888,m_6889,S3_6890>@M[Orig][LHSCase]@ rem br[{526,525}] * 
                              y'::dll<Anon_6891,n_6892,S4_6893>@M[Orig][LHSCase]@ rem br[{526,525}]&
                              (
                              ([m=m_6889 & 0<=m][n=n_6892 & 0<=n][S1=S4_6893]
                               [S2=S3_6890][y=x'][x=y'][Anon_6888=Anon_31]
                               [Anon_6891=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (543,6)  (239,13)  (239,4)  (342,4)  (342,11)  (352,6)  (352,13)  (351,6)  (351,6)  (349,6)  (349,13)  (348,8)  (347,27)  (347,14)  (347,9)  (346,10)  (346,4)  (345,8)  (345,12)  (345,4)  (345,4) )

Total verification time: 33.29 second(s)
	Time spent in main process: 4.51 second(s)
	Time spent in child processes: 28.78 second(s)
