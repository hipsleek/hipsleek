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
!!! NEW RELS:[ (exists(S1_1421:exists(v_1419:exists(S1_1387:exists(v_1289:exists(v_1384:exists(S1_1292:(S2= | 
  S2=union(S1_1421,{v_1419})) & S=union(S1_1387,{v_1384}) & S1=union(S1_1292,
  {v_1289}) & S2=S1_1387 & v_1289=v_1384 & S1_1292=))))))) --> APP(S,S1,S2),
 (exists(S1_1481:exists(v_1479:exists(S1_1292:exists(v_1289:exists(S1_1449:exists(v_1446:S_1445=union(S1_1481,
  {v_1479}) & S_1445=S1_1449 & v_1289=v_1446 & S1_1292=S1_1331 & 
  S2=S2_1333 & APP(S_1445,S1_1331,S2_1333) & S1=union(S1_1292,{v_1289}) & 
  S=union(S1_1449,{v_1446})))))))) --> APP(S,S1,S2)]
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
!!! NEW RELS:[ (exists(S1_1557:exists(v_1554:S1_1557= & S1_1557= & v=v_1554 & 
  S=union(S1_1557,{v_1554})))) --> CL(S,v),
 (exists(S1_1604:exists(v_1602:exists(S1_1571:exists(v_1568:S_1566=union(S1_1604,
  {v_1602}) & S_1566=S1_1571 & v=v_1568 & CL(S_1566,v) & S=union(S1_1571,
  {v_1568})))))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    S](ex)x::ll2<m,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_131,
                                S1: x'::ll2<n_131,S1>@M[Orig][LHSCase]&
                                n_131=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; S](ex)x::ll2<m,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              x::ll2<m,S>@M[Orig][LHSCase] * 
                              x'::ll2<n_131,S1>@M[Orig][LHSCase]&n_131=0 & 
                              n=0 & x'=null & S1= & 0<=m&
                              {FLOW,(20,21)=__norm}
                              or x::ll2<m,S>@M[Orig][LHSCase] * 
                                 x'::ll2<n_131,S1>@M[Orig][LHSCase]&S=S1 & 
                                 n_131=n_108_1691 & n=n_108_1691 & 
                                 1<=n_108_1691 & 534::forall(_x:_x <notin> S
                                  | _x=v) & 0<=m&{FLOW,(20,21)=__norm}
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
!!! NEW RELS:[ (exists(S1_1876:exists(v_1874:exists(v_1727:exists(v_1836:exists(S1_1839:exists(S1_1730:exists(S1_1760:exists(v_1757:(S1_1760= | 
  S1_1760=union(S1_1876,{v_1874})) & S1=union(S1_1839,{v_1836}) & 
  S=union(S1_1730,{v_1727}) & v_1727=v_1836 & S1_1760=S1_1839 & 
  S1_1730=union(S1_1760,{v_1757})))))))))) --> DEL(S,S1),
 (exists(S1_1917:exists(v_1915:exists(S1_1788:exists(v_1785:exists(v_1888:exists(S1_1891:(S1_1886= | 
  S1_1886=union(S1_1917,{v_1915})) & S1=union(S1_1891,{v_1888}) & 
  S=union(S1_1788,{v_1785}) & DEL(S_1801,S1_1886) & S1_1788=S_1801 & 
  v_1785=v_1888 & S1_1886=S1_1891))))))) --> DEL(S,S1)]
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
 (exists(S1_2089:exists(v_2087:exists(S1_1974:exists(v_1971:(S1_1974= | 
  S1_1974=union(S1_2089,{v_2087})) & S=union(S1_1974,{v_1971}) & 
  S1_1974=S1 & a=v_1971))))) --> DEL2(a,S,S1),
 (exists(m_1973:exists(n_2011:exists(v_node_220_903':exists(v_node_220_2099:exists(m_2097:exists(m:exists(m_2102:exists(m_2134:exists(n:exists(v_bool_216_905':exists(v_bool_219_904':exists(x:exists(r_2101:exists(res:exists(S1_2135:exists(v_2133:exists(S1_2103:exists(v_2100:exists(S1_1974:exists(v_1971:(S1_2098= & 
  (S1_1974=S_2012 & 1+m_1973=n & 1+n_2011=n & v_node_220_903'=res & 
  v_1971=v_2100 & v_node_220_2099=r_2101 & m_2097=0 & S1_2098=S1_2103 & 
  m=1 & m_2102=0 & !(v_bool_216_905') & (1+a)<=v_2100 & !(v_bool_219_904') & 
  r_2101=null & x!=null & res!=null & 1<=n & DEL2(a,S_2012,S1_2098) | 
  S1_1974=S_2012 & 1+m_1973=n & 1+n_2011=n & v_node_220_903'=res & 
  v_1971=v_2100 & v_node_220_2099=r_2101 & m_2097=0 & S1_2098=S1_2103 & 
  m=1 & m_2102=0 & !(v_bool_216_905') & !(v_bool_219_904') & r_2101=null & 
  (1+v_2100)<=a & x!=null & res!=null & 1<=n & DEL2(a,S_2012,S1_2098)) | 
  (S1_1974=S_2012 & 1+m_1973=n & 1+n_2011=n & v_node_220_903'=res & 
  v_1971=v_2100 & v_node_220_2099=r_2101 & -1+m_2097=m_2134 & 
  S1_2098=S1_2103 & -2+m=m_2134 & -1+m_2102=m_2134 & 0<=m_2134 & (2+
  m_2134)<=n & !(v_bool_216_905') & (1+a)<=v_2100 & !(v_bool_219_904') & 
  x!=null & r_2101!=null & res!=null & DEL2(a,S_2012,S1_2098) | 
  S1_1974=S_2012 & 1+m_1973=n & 1+n_2011=n & v_node_220_903'=res & 
  v_1971=v_2100 & v_node_220_2099=r_2101 & -1+m_2097=m_2134 & 
  S1_2098=S1_2103 & -2+m=m_2134 & -1+m_2102=m_2134 & 0<=m_2134 & (2+
  m_2134)<=n & !(v_bool_216_905') & !(v_bool_219_904') & (1+v_2100)<=a & 
  x!=null & r_2101!=null & res!=null & DEL2(a,S_2012,S1_2098)) & 
  S1_2098=union(S1_2135,{v_2133})) & S1=union(S1_2103,{v_2100}) & 
  S=union(S1_1974,{v_1971})))))))))))))))))))))) --> DEL2(a,S,S1)]
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
!!! NEW RELS:[ (exists(S1_2396:exists(v_2394:exists(S1_2307:exists(v:exists(v_2304:(S1_2307= | 
  S1_2307=union(S1_2396,{v_2394})) & S=union(S1_2307,{v_2304}) & (1+v)<=m & 
  v_2304=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2307:exists(v_2304:v_2304<=v & S1_2307=S_2354 & 
  m_2406=m & (1+v)<=m & FGE(S_2354,m_2406) & S=union(S1_2307,
  {v_2304}))))) --> FGE(S,m)]
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
                                EXISTS(flted_136_121,flted_136_122,S1,
                                S2: x'::ll2<flted_136_122,S1>@M[Orig][LHSCase] * 
                                res::ll2<flted_136_121,S2>@M[Orig][LHSCase]&
                                flted_136_122=1 & flted_136_121+1=n & 
                                GN(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 27::ref [x]
                              x'::ll2<flted_136_122,S1>@M[Orig][LHSCase] * 
                              res::ll2<flted_136_121,S2>@M[Orig][LHSCase]&
                              flted_136_122=1 & flted_136_121+1=n & union(S1,
                              S2)=S & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2490:exists(v_2488:exists(S1_2448:exists(v_2445:exists(v_2456:exists(S1_2459:(S1_2448= | 
  S1_2448=union(S1_2490,{v_2488})) & S1=union(S1_2459,{v_2456}) & 
  S=union(S1_2448,{v_2445}) & S1_2448=S2 & v_2445=v_2456 & S1_2459= & 
  S1_2459=))))))) --> GN(S,S1,S2)]
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
                                EXISTS(flted_175_114,
                                S2: res::ll2<flted_175_114,S2>@M[Orig][LHSCase]&
                                flted_175_114+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  2<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              res::ll2<flted_175_114,S2>@M[Orig][LHSCase]&
                              flted_175_114+2=n & S2<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2581:exists(v_2579:exists(v_2519:exists(S1_2522:exists(S1_2552:exists(v_2549:(S1_2552= | 
  S1_2552=union(S1_2581,{v_2579})) & S=union(S1_2522,{v_2519}) & 
  S1_2552=S2 & S1_2522=union(S1_2552,{v_2549})))))))) --> GNN(S,S2)]
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
                                EXISTS(flted_185_111,
                                S1: x::ll2<flted_185_111,S1>@M[Orig][LHSCase]&
                                flted_185_111=1+n & INS(S,S1,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              x::ll2<flted_185_111,S1>@M[Orig][LHSCase]&
                              flted_185_111=1+n & S1=union(S,{a}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2696:exists(v_2693:exists(S1_2618:exists(v_2615:exists(S1_2686:exists(v_2683:S1_2696= & 
  S1_2696= & S1_2686=union(S1_2696,{v_2693}) & S1_2686=union(S1_2696,
  {v_2693}) & S1_2618= & v_2615=v_2683 & a=v_2693 & S=union(S1_2618,
  {v_2615}) & S1=union(S1_2686,{v_2683})))))))) --> INS(S,S1,a),
 (exists(S1_2760:exists(v_2758:exists(S1_2618:exists(v_2615:exists(S1_2728:exists(v_2725:S1_2724=union(S1_2760,
  {v_2758}) & S1_2724=S1_2728 & v_2615=v_2725 & S1_2618=S_2650 & 
  INS(S_2650,S1_2724,a) & S=union(S1_2618,{v_2615}) & S1=union(S1_2728,
  {v_2725})))))))) --> INS(S,S1,a)]
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
 (exists(S1_2939:exists(v_2937:exists(S1_2936:exists(v_2934:exists(S1_2803:exists(v_2890:exists(v_2800:exists(S1_2893:exists(S_94:exists(S1_2850:exists(v_2847:(S_2807= & 
  S2_2842= | S2_2842=union(S1_2939,{v_2937}) & S_2807=union(S1_2936,
  {v_2934})) & S2=union(S1_2893,{v_2890}) & S=union(S1_2803,{v_2800}) & 
  CPY(S_2807,S2_2842) & S1_2850=S1_2803 & S_2807=S1_2803 & v_2890=v_2847 & 
  v_2800=v_2847 & S2_2842=S1_2893 & S_94=union(S1_2850,
  {v_2847}))))))))))))) --> CPY(S,S2),
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
 (exists(S1_3212:exists(v_3210:exists(v_3027:exists(S1_3030:exists(Anon_11:exists(v:(S2_3181= | 
  S2_3181=union(S1_3212,{v_3210})) & S=union(S1_3030,{v_3027}) & 
  FIL(S_3084,S2_3181) & S2_3181=S2 & v_3027=v & S1_3030=S_3084 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(m_3029:exists(n_3126:exists(res:exists(v_node_382_727':exists(tmp_90':exists(m_3170:exists(m:exists(m_3223:exists(m_3255:exists(n:exists(v_bool_369_725':exists(v:exists(r_3222:exists(x:exists(v_bool_368_726':exists(S1_3256:exists(v_3254:exists(S1_3224:exists(v_3221:exists(S1_3030:exists(v_3027:(S2_3171= & 
  (S1_3030=S_3127 & 1+m_3029=n & 1+n_3126=n & res=x & v_node_382_727'=x & 
  v_3027=v_3221 & tmp_90'=r_3222 & m_3170=0 & S2_3171=S1_3224 & m=1 & 
  m_3223=0 & (1+v)<=v_3221 & !(v_bool_369_725') & r_3222=null & x!=null & 
  1<=n & FIL(S_3127,S2_3171) & v_bool_368_726' | S1_3030=S_3127 & 1+
  m_3029=n & 1+n_3126=n & res=x & v_node_382_727'=x & v_3027=v_3221 & 
  tmp_90'=r_3222 & m_3170=0 & S2_3171=S1_3224 & m=1 & m_3223=0 & 
  !(v_bool_369_725') & r_3222=null & (1+v_3221)<=v & x!=null & 1<=n & 
  FIL(S_3127,S2_3171) & v_bool_368_726') | (S1_3030=S_3127 & 1+m_3029=n & 1+
  n_3126=n & res=x & v_node_382_727'=x & v_3027=v_3221 & tmp_90'=r_3222 & -1+
  m_3170=m_3255 & S2_3171=S1_3224 & -2+m=m_3255 & -1+m_3223=m_3255 & 
  0<=m_3255 & (2+m_3255)<=n & (1+v)<=v_3221 & !(v_bool_369_725') & 
  r_3222!=null & x!=null & FIL(S_3127,S2_3171) & v_bool_368_726' | 
  S1_3030=S_3127 & 1+m_3029=n & 1+n_3126=n & res=x & v_node_382_727'=x & 
  v_3027=v_3221 & tmp_90'=r_3222 & -1+m_3170=m_3255 & S2_3171=S1_3224 & -2+
  m=m_3255 & -1+m_3223=m_3255 & 0<=m_3255 & (2+m_3255)<=n & 
  !(v_bool_369_725') & (1+v_3221)<=v & r_3222!=null & x!=null & 
  FIL(S_3127,S2_3171) & v_bool_368_726') & S2_3171=union(S1_3256,
  {v_3254})) & S2=union(S1_3224,{v_3221}) & S=union(S1_3030,
  {v_3027}))))))))))))))))))))))) --> FIL(S,S2),
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
 (exists(S1_3846:exists(v_3844:exists(S1_3709:exists(v_3706:exists(Anon_11:exists(v:(S1_3709= | 
  S1_3709=union(S1_3846,{v_3844})) & S=union(S1_3709,{v_3706}) & 
  S1_3709=S2 & v_3706=v & Anon_11=v))))))) --> RMV2(S,S2),
 (exists(m_3708:exists(n_3766:exists(res:exists(v_node_357_750':exists(tmp_91':exists(m_3811:exists(m:exists(m_3853:exists(m_3885:exists(n:exists(v_bool_346_748':exists(v:exists(r_3852:exists(x:exists(v_bool_345_749':exists(S1_3886:exists(v_3884:exists(S1_3854:exists(v_3851:exists(S1_3709:exists(v_3706:(S2_3812= & 
  (S1_3709=S_3767 & 1+m_3708=n & 1+n_3766=n & res=x & v_node_357_750'=x & 
  v_3706=v_3851 & tmp_91'=r_3852 & m_3811=0 & S2_3812=S1_3854 & m=1 & 
  m_3853=0 & (1+v)<=v_3851 & !(v_bool_346_748') & r_3852=null & x!=null & 
  1<=n & RMV2(S_3767,S2_3812) & v_bool_345_749' | S1_3709=S_3767 & 1+
  m_3708=n & 1+n_3766=n & res=x & v_node_357_750'=x & v_3706=v_3851 & 
  tmp_91'=r_3852 & m_3811=0 & S2_3812=S1_3854 & m=1 & m_3853=0 & 
  !(v_bool_346_748') & r_3852=null & (1+v_3851)<=v & x!=null & 1<=n & 
  RMV2(S_3767,S2_3812) & v_bool_345_749') | (S1_3709=S_3767 & 1+m_3708=n & 1+
  n_3766=n & res=x & v_node_357_750'=x & v_3706=v_3851 & tmp_91'=r_3852 & -1+
  m_3811=m_3885 & S2_3812=S1_3854 & -2+m=m_3885 & -1+m_3853=m_3885 & 
  0<=m_3885 & (2+m_3885)<=n & (1+v)<=v_3851 & !(v_bool_346_748') & 
  r_3852!=null & x!=null & RMV2(S_3767,S2_3812) & v_bool_345_749' | 
  S1_3709=S_3767 & 1+m_3708=n & 1+n_3766=n & res=x & v_node_357_750'=x & 
  v_3706=v_3851 & tmp_91'=r_3852 & -1+m_3811=m_3885 & S2_3812=S1_3854 & -2+
  m=m_3885 & -1+m_3853=m_3885 & 0<=m_3885 & (2+m_3885)<=n & 
  !(v_bool_346_748') & (1+v_3851)<=v & r_3852!=null & x!=null & 
  RMV2(S_3767,S2_3812) & v_bool_345_749') & S2_3812=union(S1_3886,
  {v_3884})) & S2=union(S1_3854,{v_3851}) & S=union(S1_3709,
  {v_3706}))))))))))))))))))))))) --> RMV2(S,S2),
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
 (exists(S1_4055:exists(v_4053:exists(S1_3991:exists(v_3988:exists(v_4023:exists(S1_4026:(S2_4022= | 
  S2_4022=union(S1_4055,{v_4053})) & S2=union(S1_4026,{v_4023}) & 
  S1=union(S1_3991,{v_3988}) & TRAV(S1_3995,S2_4022) & S1_3991=S1_3995 & 
  v_3988=v_4023 & S2_4022=S1_4026))))))) --> TRAV(S1,S2),
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
                                EXISTS(flted_101_126,
                                S2: x'::ll2<flted_101_126,S2>@M[Orig][LHSCase]&
                                flted_101_126+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              x'::ll2<flted_101_126,S2>@M[Orig][LHSCase]&
                              flted_101_126+1=m & S2<subset> S1  & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4147:exists(v_4145:exists(v_4115:exists(S1_4118:(S1_4118= | 
  S1_4118=union(S1_4147,{v_4145})) & S1=union(S1_4118,{v_4115}) & 
  S1_4118=S2))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_90_129,
                                S1: x'::ll2<flted_90_129,S1>@M[Orig][LHSCase]&
                                flted_90_129=1+n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::ll2<flted_90_129,S1>@M[Orig][LHSCase]&
                              tmp_130_4187'=x' & v=v_4161_4191 & 
                              x=r_4162_4188 & S=S1_4164_4190 & 
                              flted_90_129=1+m_4163_4189 & n=m_4163_4189 & 
                              S1=union(S1_4164_4190,{v_4161_4191}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
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
!!! REL :  REV(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                    ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 55::ref [xs;ys]
                                EXISTS(flted_251_106,
                                S: ys'::ll2<flted_251_106,S>@M[Orig][LHSCase]&
                                flted_251_106=m+n & xs'=null & REV(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                  ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 55::ref [xs;ys]
                              ys'::ll2<flted_251_106,S>@M[Orig][LHSCase]&
                              flted_251_106=m+n & xs'=null & S=union(S1,
                              S2) & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4437:exists(v_4435:exists(v_4320:exists(S1_4323:exists(S1_4291:exists(v_4288:S2_4306=union(S1_4323,
  {v_4320}) & S_4400=union(S1_4437,{v_4435}) & v_4288=v_4320 & 
  S1_4291=S1_4304 & S2=S1_4323 & S_4400=S & REV(S_4400,S1_4304,S2_4306) & 
  S1=union(S1_4291,{v_4288})))))))) --> REV(S,S1,S2),
 (exists(S1_4483:exists(v_4481:(S2= | S2=union(S1_4483,{v_4481})) & S1= & 
  S2=S))) --> REV(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                    S](ex)x::node<v,t>@M[Orig] * 
                    t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                    y::ll2<j,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(S2,k: x::ll2<k,S2>@M[Orig][LHSCase]&
                                1<=k & k=1+j&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig] * 
                  t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                  y::ll2<j,S>@M[Orig][LHSCase]&x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                              x::ll2<k,S2>@M[Orig][LHSCase]&x=x' & 
                              v=v_4509_4551 & y=r_4510_4548 & 
                              S=S1_4512_4550 & k=1+m_4511_4549 & 
                              j=m_4511_4549 & x'!=null & 0<=m_4511_4549 & 
                              S2=union(S1_4512_4550,{v_4509_4551}) & 
                              0<=Anon_16 & 0<=j&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
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
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPI]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 96::ref [x]
                                EXISTS(flted_410_87,
                                S: x'::ll2<flted_410_87,S>@M[Orig][LHSCase]&
                                flted_410_87=n+m & SPI(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 96::ref [x]
                              x'::ll2<flted_410_87,S>@M[Orig][LHSCase]&
                              flted_410_87=n+m & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5043:exists(v_5041:(S2= | S2=union(S1_5043,{v_5041})) & S1= & 
  S2=S))) --> SPI(S,S1,S2),
 (exists(S1_5122:exists(v_5120:exists(S1_4896:exists(S1_4931:exists(v_4893:exists(v_5059:exists(v_4928:exists(S1_5062:exists(S1_5072:exists(v_5069:(S_5009= | 
  S_5009=union(S1_5122,{v_5120})) & S=union(S1_5062,{v_5059}) & 
  S1=union(S1_4896,{v_4893}) & S2=union(S1_4931,{v_4928}) & 
  SPI(S_5009,S1_4938,S2_4940) & S1_4896=S1_4938 & S1_4931=S2_4940 & 
  v_4893=v_5059 & v_4928=v_5069 & S_5009=S1_5072 & S1_5062=union(S1_5072,
  {v_5069}) & S1_5062=union(S1_5072,{v_5069})))))))))))) --> SPI(S,S1,S2),
 (exists(S1_5167_5170:exists(v_5168:S1=S & S2= & S1=union(S1_5167_5170,
  {v_5168})))) --> SPI(S,S1,S2)]
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
!!! NEW RELS:[ (exists(S1_5355:exists(v_5353:exists(S1_5232:exists(v_5229:exists(S1_5326:exists(v_5323:S1_5326= & 
  S1_5326= & S1_5232=union(S1_5355,{v_5353}) & v_5229=v_5323 & S1_5232=S2 & 
  S=union(S1_5232,{v_5229}) & S1=union(S1_5326,
  {v_5323})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_5458:exists(v_5456:exists(S1_5461:exists(v_5459:exists(S1_5272:exists(v_5269:exists(S1_5375:exists(v_5372:S1_5368=union(S1_5458,
  {v_5456}) & S2_5369=union(S1_5461,{v_5459}) & S1_5368=S1_5375 & 
  v_5269=v_5372 & S1_5272=S_5274 & S2_5369=S2 & 
  SPLIT(S_5274,S1_5368,S2_5369) & S=union(S1_5272,{v_5269}) & 
  S1=union(S1_5375,{v_5372})))))))))) --> SPLIT(S,S1,S2)]
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


12 false contexts at: ( (159,13)  (159,4)  (237,4)  (237,11)  (242,4)  (242,11)  (241,10)  (241,4)  (240,8)  (240,12)  (240,4)  (240,4) )

Total verification time: 25.05 second(s)
	Time spent in main process: 2.6 second(s)
	Time spent in child processes: 22.45 second(s)
