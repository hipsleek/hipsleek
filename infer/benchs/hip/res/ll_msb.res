/usr/local/bin/mona

Processing file "ll_msb.ss"
Parsing ll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure append$node~node... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[n1; S1; n2; 
                    S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase] * 
                    y::ll2<n2,S2>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(m,S: x::ll2<m,S>@M[Orig][LHSCase]&
                                m=n2+n1 & APP(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase] * 
                  y::ll2<n2,S2>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              x::ll2<m,S>@M[Orig][LHSCase]&m=n2+n1 & 
                              union(S1,S2)=S & 0<=n1 & 0<=n2&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1427:exists(v_1425:exists(S1_1393:exists(v_1295:exists(v_1390:exists(S1_1298:(S2= | 
  S2=union(S1_1427,{v_1425})) & S=union(S1_1393,{v_1390}) & S1=union(S1_1298,
  {v_1295}) & S2=S1_1393 & v_1295=v_1390 & S1_1298=))))))) --> APP(S,S1,S2),
 (exists(S1_1487:exists(v_1485:exists(S1_1298:exists(v_1295:exists(S1_1455:exists(v_1452:S_1451=union(S1_1487,
  {v_1485}) & S_1451=S1_1455 & v_1295=v_1452 & S1_1298=S1_1337 & 
  S2=S2_1339 & APP(S_1451,S1_1337,S2_1339) & S1=union(S1_1298,{v_1295}) & 
  S=union(S1_1455,{v_1452})))))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
!!! REL :  CL(S,v)
!!! POST:  forall(_x:_x <notin> S  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&0<=n&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 48::
                                                         true&res=null&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 49::
                                                         EXISTS(n_108,
                                                         S: res::ll2<n_108,S>@M[Orig][LHSCase]&
                                                         CL(S,v) & n_108=n&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 50::
                                                         true&true&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&0<=n&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 48::
                                                       true&res=null & n=0&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 49::
                                                       res::ll2<n_108,S>@M[Orig][LHSCase]&
                                                       n_108=n & 
                                                       forall(_x:_x <notin> S
                                                        | _x=v) & 0<n&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           n<0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 50::
                                                       true&n<0&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_1563:exists(v_1560:S1_1563= & S1_1563= & v=v_1560 & 
  S=union(S1_1563,{v_1560})))) --> CL(S,v),
 (exists(S1_1610:exists(v_1608:exists(S1_1577:exists(v_1574:S_1572=union(S1_1610,
  {v_1608}) & S_1572=S1_1577 & v=v_1574 & CL(S_1572,v) & S=union(S1_1577,
  {v_1574})))))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_131,
                                S4: x'::ll2<n_131,S4>@M[Orig][LHSCase]&
                                n_131=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              x::ll2<m,S3>@M[Orig][LHSCase] * 
                              x'::ll2<n_131,S4>@M[Orig][LHSCase]&n_131=0 & 
                              n=0 & x'=null & S4= & 0<=m&
                              {FLOW,(20,21)=__norm}
                              or x::ll2<m,S3>@M[Orig][LHSCase] * 
                                 x'::ll2<n_131,S4>@M[Orig][LHSCase]&
                                 S_1698=S4 & n_131=n_108_1697 & 
                                 n=n_108_1697 & 1<=n_108_1697 & 
                                 534::forall(_x:_x <notin> S_1698  | _x=v) & 
                                 0<=m&{FLOW,(20,21)=__norm}
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
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(m,S1: x::ll2<m,S1>@M[Orig][LHSCase]&
                                DEL(S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              x::ll2<m,S1>@M[Orig][LHSCase]&S1<subset> S  & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1883:exists(v_1881:exists(v_1734:exists(v_1843:exists(S1_1846:exists(S1_1737:exists(S1_1767:exists(v_1764:(S1_1767= | 
  S1_1767=union(S1_1883,{v_1881})) & S1=union(S1_1846,{v_1843}) & 
  S=union(S1_1737,{v_1734}) & v_1734=v_1843 & S1_1767=S1_1846 & 
  S1_1737=union(S1_1767,{v_1764})))))))))) --> DEL(S,S1),
 (exists(S1_1924:exists(v_1922:exists(S1_1795:exists(v_1792:exists(v_1895:exists(S1_1898:(S1_1893= | 
  S1_1893=union(S1_1924,{v_1922})) & S1=union(S1_1898,{v_1895}) & 
  S=union(S1_1795,{v_1792}) & DEL(S_1808,S1_1893) & S1_1795=S_1808 & 
  v_1792=v_1895 & S1_1893=S1_1898))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL2(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  a <notin> S  | a <in> S 
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(m,S1: res::ll2<m,S1>@M[Orig][LHSCase]&
                                m<=n & DEL2(a,S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&(a <notin> S  | a <in> S ) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 45::
                              res::ll2<m,S1>@M[Orig][LHSCase]&m<=n & (S1=S & 
                              a <notin> S  | S1<subset> S  & a <in> S ) & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S1= & S= & S1=S) --> DEL2(a,S,S1),
 (S1=S & S= & S1=) --> DEL2(a,S,S1),
 (exists(S1_2096:exists(v_2094:exists(S1_1981:exists(v_1978:(S1_1981= | 
  S1_1981=union(S1_2096,{v_2094})) & S=union(S1_1981,{v_1978}) & 
  S1_1981=S1 & a=v_1978))))) --> DEL2(a,S,S1),
 (exists(m_1980:exists(n_2018:exists(v_node_224_909':exists(v_node_224_2106:exists(m_2104:exists(m:exists(m_2109:exists(m_2141:exists(n:exists(v_bool_220_911':exists(v_bool_223_910':exists(x:exists(r_2108:exists(res:exists(S1_2142:exists(v_2140:exists(S1_2110:exists(v_2107:exists(S1_1981:exists(v_1978:(S1_2105= & 
  (S1_1981=S_2019 & 1+m_1980=n & 1+n_2018=n & v_node_224_909'=res & 
  v_1978=v_2107 & v_node_224_2106=r_2108 & m_2104=0 & S1_2105=S1_2110 & 
  m=1 & m_2109=0 & !(v_bool_220_911') & (1+a)<=v_2107 & !(v_bool_223_910') & 
  r_2108=null & x!=null & res!=null & 1<=n & DEL2(a,S_2019,S1_2105) | 
  S1_1981=S_2019 & 1+m_1980=n & 1+n_2018=n & v_node_224_909'=res & 
  v_1978=v_2107 & v_node_224_2106=r_2108 & m_2104=0 & S1_2105=S1_2110 & 
  m=1 & m_2109=0 & !(v_bool_220_911') & !(v_bool_223_910') & r_2108=null & 
  (1+v_2107)<=a & x!=null & res!=null & 1<=n & DEL2(a,S_2019,S1_2105)) | 
  (S1_1981=S_2019 & 1+m_1980=n & 1+n_2018=n & v_node_224_909'=res & 
  v_1978=v_2107 & v_node_224_2106=r_2108 & -1+m_2104=m_2141 & 
  S1_2105=S1_2110 & -2+m=m_2141 & -1+m_2109=m_2141 & 0<=m_2141 & (2+
  m_2141)<=n & !(v_bool_220_911') & (1+a)<=v_2107 & !(v_bool_223_910') & 
  x!=null & r_2108!=null & res!=null & DEL2(a,S_2019,S1_2105) | 
  S1_1981=S_2019 & 1+m_1980=n & 1+n_2018=n & v_node_224_909'=res & 
  v_1978=v_2107 & v_node_224_2106=r_2108 & -1+m_2104=m_2141 & 
  S1_2105=S1_2110 & -2+m=m_2141 & -1+m_2109=m_2141 & 0<=m_2141 & (2+
  m_2141)<=n & !(v_bool_220_911') & !(v_bool_223_910') & (1+v_2107)<=a & 
  x!=null & r_2108!=null & res!=null & DEL2(a,S_2019,S1_2105)) & 
  S1_2105=union(S1_2142,{v_2140})) & S1=union(S1_2110,{v_2107}) & 
  S=union(S1_1981,{v_1978})))))))))))))))))))))) --> DEL2(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 93::
                                
                                true&res=null&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_22,
                                   m: res::node<m,Anon_22>@M[Orig]&v<m & 
                                   FGE(S,m)&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 93::
                              
                              true&res=null & 0<=n&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_22>@M[Orig]&v<m & 
                                 {m}<subset> S  & 0<=n&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(S1_2403:exists(v_2401:exists(S1_2314:exists(v:exists(v_2311:(S1_2314= | 
  S1_2314=union(S1_2403,{v_2401})) & S=union(S1_2314,{v_2311}) & (1+v)<=m & 
  v_2311=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2314:exists(v_2311:v_2311<=v & S1_2314=S_2361 & 
  m_2413=m & (1+v)<=m & FGE(S_2361,m_2413) & S=union(S1_2314,
  {v_2311}))))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  GN(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::ref [x]
                                EXISTS(flted_138_121,flted_138_122,S1,
                                S2: x'::ll2<flted_138_122,S1>@M[Orig][LHSCase] * 
                                res::ll2<flted_138_121,S2>@M[Orig][LHSCase]&
                                flted_138_122=1 & flted_138_121+1=n & 
                                GN(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 27::ref [x]
                              x'::ll2<flted_138_122,S1>@M[Orig][LHSCase] * 
                              res::ll2<flted_138_121,S2>@M[Orig][LHSCase]&
                              flted_138_122=1 & flted_138_121+1=n & union(S1,
                              S2)=S & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2497:exists(v_2495:exists(S1_2455:exists(v_2452:exists(v_2463:exists(S1_2466:(S1_2455= | 
  S1_2455=union(S1_2497,{v_2495})) & S1=union(S1_2466,{v_2463}) & 
  S=union(S1_2455,{v_2452}) & S1_2455=S2 & v_2452=v_2463 & S1_2466= & 
  S1_2466=))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&1<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(flted_178_114,
                                S2: res::ll2<flted_178_114,S2>@M[Orig][LHSCase]&
                                flted_178_114+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  2<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              res::ll2<flted_178_114,S2>@M[Orig][LHSCase]&
                              flted_178_114+2=n & S2<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2588:exists(v_2586:exists(v_2526:exists(S1_2529:exists(S1_2559:exists(v_2556:(S1_2559= | 
  S1_2559=union(S1_2588,{v_2586})) & S=union(S1_2529,{v_2526}) & 
  S1_2559=S2 & S1_2529=union(S1_2559,{v_2556})))))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_188_111,
                                S1: x::ll2<flted_188_111,S1>@M[Orig][LHSCase]&
                                flted_188_111=1+n & INS(S,S1,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              x::ll2<flted_188_111,S1>@M[Orig][LHSCase]&
                              flted_188_111=1+n & S1=union(S,{a}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2703:exists(v_2700:exists(S1_2625:exists(v_2622:exists(S1_2693:exists(v_2690:S1_2703= & 
  S1_2703= & S1_2693=union(S1_2703,{v_2700}) & S1_2693=union(S1_2703,
  {v_2700}) & S1_2625= & v_2622=v_2690 & a=v_2700 & S=union(S1_2625,
  {v_2622}) & S1=union(S1_2693,{v_2690})))))))) --> INS(S,S1,a),
 (exists(S1_2767:exists(v_2765:exists(S1_2625:exists(v_2622:exists(S1_2735:exists(v_2732:S1_2731=union(S1_2767,
  {v_2765}) & S1_2731=S1_2735 & v_2622=v_2732 & S1_2625=S_2657 & 
  INS(S_2657,S1_2731,a) & S=union(S1_2625,{v_2622}) & S1=union(S1_2735,
  {v_2732})))))))) --> INS(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CPY(S,S2)
!!! POST:  S2=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 71::
                                EXISTS(n_93,S_94,n_95,
                                S2: x::ll2<n_93,S_94>@M[Orig][LHSCase] * 
                                res::ll2<n_95,S2>@M[Orig][LHSCase]&
                                CPY(S,S2) & n_93=n & S_94=S & n_95=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 71::
                              x::ll2<n_93,S_94>@M[Orig][LHSCase] * 
                              res::ll2<n_95,S2>@M[Orig][LHSCase]&n_93=n & 
                              S_94=S & n_95=n & S2=S & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S_94:S2= & S= & S_94=S & S_94= & S_94=)) --> CPY(S,S2),
 (exists(S1_2946:exists(v_2944:exists(S1_2943:exists(v_2941:exists(S1_2810:exists(v_2897:exists(v_2807:exists(S1_2900:exists(S_94:exists(S1_2857:exists(v_2854:(S_2814= & 
  S2_2849= | S2_2849=union(S1_2946,{v_2944}) & S_2814=union(S1_2943,
  {v_2941})) & S2=union(S1_2900,{v_2897}) & S=union(S1_2810,{v_2807}) & 
  CPY(S_2814,S2_2849) & S1_2857=S1_2810 & S_2814=S1_2810 & v_2897=v_2854 & 
  v_2807=v_2854 & S2_2849=S1_2900 & S_94=union(S1_2857,
  {v_2854}))))))))))))) --> CPY(S,S2),
 (exists(S_94:S_94= & S_94=S & S= & S2=)) --> CPY(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FIL(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::
                                EXISTS(m,S2: res::ll2<m,S2>@M[Orig][LHSCase]&
                                m<=n & FIL(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 85::
                              res::ll2<m,S2>@M[Orig][LHSCase]&m<=n & 
                              S2<subset> S  & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S= & S2=S) --> FIL(S,S2),
 (exists(S1_3219:exists(v_3217:exists(v_3034:exists(S1_3037:exists(Anon_11:exists(v:(S2_3188= | 
  S2_3188=union(S1_3219,{v_3217})) & S=union(S1_3037,{v_3034}) & 
  FIL(S_3091,S2_3188) & S2_3188=S2 & v_3034=v & S1_3037=S_3091 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(m_3036:exists(n_3133:exists(res:exists(v_node_386_733':exists(tmp_90':exists(m_3177:exists(m:exists(m_3230:exists(m_3262:exists(n:exists(v_bool_373_731':exists(v:exists(r_3229:exists(x:exists(v_bool_372_732':exists(S1_3263:exists(v_3261:exists(S1_3231:exists(v_3228:exists(S1_3037:exists(v_3034:(S2_3178= & 
  (S1_3037=S_3134 & 1+m_3036=n & 1+n_3133=n & res=x & v_node_386_733'=x & 
  v_3034=v_3228 & tmp_90'=r_3229 & m_3177=0 & S2_3178=S1_3231 & m=1 & 
  m_3230=0 & (1+v)<=v_3228 & !(v_bool_373_731') & r_3229=null & x!=null & 
  1<=n & FIL(S_3134,S2_3178) & v_bool_372_732' | S1_3037=S_3134 & 1+
  m_3036=n & 1+n_3133=n & res=x & v_node_386_733'=x & v_3034=v_3228 & 
  tmp_90'=r_3229 & m_3177=0 & S2_3178=S1_3231 & m=1 & m_3230=0 & 
  !(v_bool_373_731') & r_3229=null & (1+v_3228)<=v & x!=null & 1<=n & 
  FIL(S_3134,S2_3178) & v_bool_372_732') | (S1_3037=S_3134 & 1+m_3036=n & 1+
  n_3133=n & res=x & v_node_386_733'=x & v_3034=v_3228 & tmp_90'=r_3229 & -1+
  m_3177=m_3262 & S2_3178=S1_3231 & -2+m=m_3262 & -1+m_3230=m_3262 & 
  0<=m_3262 & (2+m_3262)<=n & (1+v)<=v_3228 & !(v_bool_373_731') & 
  r_3229!=null & x!=null & FIL(S_3134,S2_3178) & v_bool_372_732' | 
  S1_3037=S_3134 & 1+m_3036=n & 1+n_3133=n & res=x & v_node_386_733'=x & 
  v_3034=v_3228 & tmp_90'=r_3229 & -1+m_3177=m_3262 & S2_3178=S1_3231 & -2+
  m=m_3262 & -1+m_3230=m_3262 & 0<=m_3262 & (2+m_3262)<=n & 
  !(v_bool_373_731') & (1+v_3228)<=v & r_3229!=null & x!=null & 
  FIL(S_3134,S2_3178) & v_bool_372_732') & S2_3178=union(S1_3263,
  {v_3261})) & S2=union(S1_3231,{v_3228}) & S=union(S1_3037,
  {v_3034}))))))))))))))))))))))) --> FIL(S,S2),
 (S2=S & S= & S2=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RMV2(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 78::
                                EXISTS(m,S2: res::ll2<m,S2>@M[Orig][LHSCase]&
                                m<=n & RMV2(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 78::
                              res::ll2<m,S2>@M[Orig][LHSCase]&m<=n & 
                              S2<subset> S  & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S= & S2=S) --> RMV2(S,S2),
 (exists(S1_3853:exists(v_3851:exists(S1_3716:exists(v_3713:exists(Anon_11:exists(v:(S1_3716= | 
  S1_3716=union(S1_3853,{v_3851})) & S=union(S1_3716,{v_3713}) & 
  S1_3716=S2 & v_3713=v & Anon_11=v))))))) --> RMV2(S,S2),
 (exists(m_3715:exists(n_3773:exists(res:exists(v_node_361_756':exists(tmp_91':exists(m_3818:exists(m:exists(m_3860:exists(m_3892:exists(n:exists(v_bool_350_754':exists(v:exists(r_3859:exists(x:exists(v_bool_349_755':exists(S1_3893:exists(v_3891:exists(S1_3861:exists(v_3858:exists(S1_3716:exists(v_3713:(S2_3819= & 
  (S1_3716=S_3774 & 1+m_3715=n & 1+n_3773=n & res=x & v_node_361_756'=x & 
  v_3713=v_3858 & tmp_91'=r_3859 & m_3818=0 & S2_3819=S1_3861 & m=1 & 
  m_3860=0 & (1+v)<=v_3858 & !(v_bool_350_754') & r_3859=null & x!=null & 
  1<=n & RMV2(S_3774,S2_3819) & v_bool_349_755' | S1_3716=S_3774 & 1+
  m_3715=n & 1+n_3773=n & res=x & v_node_361_756'=x & v_3713=v_3858 & 
  tmp_91'=r_3859 & m_3818=0 & S2_3819=S1_3861 & m=1 & m_3860=0 & 
  !(v_bool_350_754') & r_3859=null & (1+v_3858)<=v & x!=null & 1<=n & 
  RMV2(S_3774,S2_3819) & v_bool_349_755') | (S1_3716=S_3774 & 1+m_3715=n & 1+
  n_3773=n & res=x & v_node_361_756'=x & v_3713=v_3858 & tmp_91'=r_3859 & -1+
  m_3818=m_3892 & S2_3819=S1_3861 & -2+m=m_3892 & -1+m_3860=m_3892 & 
  0<=m_3892 & (2+m_3892)<=n & (1+v)<=v_3858 & !(v_bool_350_754') & 
  r_3859!=null & x!=null & RMV2(S_3774,S2_3819) & v_bool_349_755' | 
  S1_3716=S_3774 & 1+m_3715=n & 1+n_3773=n & res=x & v_node_361_756'=x & 
  v_3713=v_3858 & tmp_91'=r_3859 & -1+m_3818=m_3892 & S2_3819=S1_3861 & -2+
  m=m_3892 & -1+m_3860=m_3892 & 0<=m_3892 & (2+m_3892)<=n & 
  !(v_bool_350_754') & (1+v_3858)<=v & r_3859!=null & x!=null & 
  RMV2(S_3774,S2_3819) & v_bool_349_755') & S2_3819=union(S1_3893,
  {v_3891})) & S2=union(S1_3861,{v_3858}) & S=union(S1_3716,
  {v_3713}))))))))))))))))))))))) --> RMV2(S,S2),
 (S2=S & S= & S2=) --> RMV2(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 68::
                                EXISTS(n_97,
                                S2: x::ll2<n_97,S2>@M[Orig][LHSCase]&
                                TRAV(S1,S2) & n_97=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 68::
                              x::ll2<n_97,S2>@M[Orig][LHSCase]&n_97=n & 
                              S1=S2 & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S1= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_4062:exists(v_4060:exists(S1_3998:exists(v_3995:exists(v_4030:exists(S1_4033:(S2_4029= | 
  S2_4029=union(S1_4062,{v_4060})) & S2=union(S1_4033,{v_4030}) & 
  S1=union(S1_3998,{v_3995}) & TRAV(S1_4002,S2_4029) & S1_3998=S1_4002 & 
  v_3995=v_4030 & S2_4029=S1_4033))))))) --> TRAV(S1,S2),
 (S2=S1 & S1= & S2=) --> TRAV(S1,S2)]
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
              EBase exists (Expl)(Impl)[m; 
                    S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(flted_102_126,
                                S2: x'::ll2<flted_102_126,S2>@M[Orig][LHSCase]&
                                flted_102_126+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              x'::ll2<flted_102_126,S2>@M[Orig][LHSCase]&
                              flted_102_126+1=m & S2<subset> S1  & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4154:exists(v_4152:exists(v_4122:exists(S1_4125:(S1_4125= | 
  S1_4125=union(S1_4154,{v_4152})) & S1=union(S1_4125,{v_4122}) & 
  S1_4125=S2))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(S1,S,v)
!!! POST:  S1=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_91_129,
                                S1: x'::ll2<flted_91_129,S1>@M[Orig][LHSCase]&
                                flted_91_129=1+n & PUF(S1,S,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::ll2<flted_91_129,S1>@M[Orig][LHSCase]&
                              flted_91_129=1+n & S1=union(S,{v}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4196:exists(v_4194:exists(S1_4171:exists(v_4168:(S= | 
  S=union(S1_4196,{v_4194})) & S1=union(S1_4171,{v_4168}) & S=S1_4171 & 
  v=v_4168))))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(n_124,
                                S2: x::ll2<n_124,S2>@M[Orig][LHSCase]&
                                n_124=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              x::ll2<n_124,S2>@M[Orig][LHSCase]&res=x & 
                              S1=S2 & n=n_124 & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  REV(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                    ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 55::ref [xs;ys]
                                EXISTS(flted_255_106,
                                S: ys'::ll2<flted_255_106,S>@M[Orig][LHSCase]&
                                flted_255_106=m+n & xs'=null & REV(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                  ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 55::ref [xs;ys]
                              ys'::ll2<flted_255_106,S>@M[Orig][LHSCase]&
                              flted_255_106=m+n & xs'=null & S=union(S1,
                              S2) & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4447:exists(v_4445:exists(v_4330:exists(S1_4333:exists(S1_4301:exists(v_4298:S2_4316=union(S1_4333,
  {v_4330}) & S_4410=union(S1_4447,{v_4445}) & v_4298=v_4330 & 
  S1_4301=S1_4314 & S2=S1_4333 & S_4410=S & REV(S_4410,S1_4314,S2_4316) & 
  S1=union(S1_4301,{v_4298})))))))) --> REV(S,S1,S2),
 (exists(S1_4493:exists(v_4491:(S2= | S2=union(S1_4493,{v_4491})) & S1= & 
  S2=S))) --> REV(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(S,S2,v)
!!! POST:  S2=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                    S](ex)x::node<v,t>@M[Orig] * 
                    t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                    y::ll2<j,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(k,S2: x::ll2<k,S2>@M[Orig][LHSCase]&
                                1<=k & k=1+j & SN(S,S2,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig] * 
                  t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                  y::ll2<j,S>@M[Orig][LHSCase]&x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              x::ll2<k,S2>@M[Orig][LHSCase]&1<=k & k=1+j & 
                              S2=union(S,{v}) & 0<=Anon_16 & 0<=j&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4556:exists(v_4554:exists(S1_4522:exists(v_4519:(S= | 
  S=union(S1_4556,{v_4554}) | S= | S=union(S1_4556,{v_4554})) & 
  S2=union(S1_4522,{v_4519}) & S=S1_4522 & v=v_4519))))) --> SN(S,S2,v)]
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

!!! REL :  SPI(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPI]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 96::ref [x]
                                EXISTS(flted_415_87,
                                S: x'::ll2<flted_415_87,S>@M[Orig][LHSCase]&
                                flted_415_87=n+m & SPI(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 96::ref [x]
                              x'::ll2<flted_415_87,S>@M[Orig][LHSCase]&
                              flted_415_87=n+m & S=union(S1,S2) & 0<=n & 
                              0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5062:exists(v_5060:(S2= | S2=union(S1_5062,{v_5060})) & S1= & 
  S2=S))) --> SPI(S,S1,S2),
 (exists(S1_5141:exists(v_5139:exists(S1_4915:exists(S1_4950:exists(v_4912:exists(v_5078:exists(v_4947:exists(S1_5081:exists(S1_5091:exists(v_5088:(S_5028= | 
  S_5028=union(S1_5141,{v_5139})) & S=union(S1_5081,{v_5078}) & 
  S1=union(S1_4915,{v_4912}) & S2=union(S1_4950,{v_4947}) & 
  SPI(S_5028,S1_4957,S2_4959) & S1_4915=S1_4957 & S1_4950=S2_4959 & 
  v_4912=v_5078 & v_4947=v_5088 & S_5028=S1_5091 & S1_5081=union(S1_5091,
  {v_5088}) & S1_5081=union(S1_5091,{v_5088})))))))))))) --> SPI(S,S1,S2),
 (exists(S1_5186_5189:exists(v_5187:S1=S & S2= & S1=union(S1_5186_5189,
  {v_5187})))) --> SPI(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<a & a<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [x]
                                EXISTS(n2,n1,S1,
                                S2: x'::ll2<n1,S1>@M[Orig][LHSCase] * 
                                res::ll2<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                                0<n1 & 0<n2 & n1=a & SPLIT(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [x]
                              x'::ll2<n1,S1>@M[Orig][LHSCase] * 
                              res::ll2<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                              0<n1 & 0<n2 & n1=a & union(S1,S2)=S & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5374:exists(v_5372:exists(S1_5251:exists(v_5248:exists(S1_5345:exists(v_5342:S1_5345= & 
  S1_5345= & S1_5251=union(S1_5374,{v_5372}) & v_5248=v_5342 & S1_5251=S2 & 
  S=union(S1_5251,{v_5248}) & S1=union(S1_5345,
  {v_5342})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_5477:exists(v_5475:exists(S1_5480:exists(v_5478:exists(S1_5291:exists(v_5288:exists(S1_5394:exists(v_5391:S1_5387=union(S1_5477,
  {v_5475}) & S2_5388=union(S1_5480,{v_5478}) & S1_5387=S1_5394 & 
  v_5288=v_5391 & S1_5291=S_5293 & S2_5388=S2 & 
  SPLIT(S_5293,S1_5387,S2_5388) & S=union(S1_5291,{v_5288}) & 
  S1=union(S1_5394,{v_5391})))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_132,n_133,S3,
                                S4: x'::ll2<m_132,S3>@M[Orig][LHSCase] * 
                                y'::ll2<n_133,S4>@M[Orig][LHSCase]&m_132=m & 
                                n_133=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::ll2<m_132,S3>@M[Orig][LHSCase] * 
                              y'::ll2<n_133,S4>@M[Orig][LHSCase]&y=x' & 
                              y'=x & S2=S3 & S1=S4 & m=m_132 & n=n_133 & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (162,13)  (162,4)  (241,4)  (241,11)  (246,4)  (246,11)  (245,10)  (245,4)  (244,8)  (244,12)  (244,4)  (244,4) )

Total verification time: 24.38 second(s)
	Time spent in main process: 2.54 second(s)
	Time spent in child processes: 21.84 second(s)
