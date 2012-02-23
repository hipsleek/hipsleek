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
!!! POST:  true
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
                                                       n_108=n & 0<n&
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
                                 n=n_131 & 1<=n_131 & 0<=m&
                                 {FLOW,(20,21)=__norm}
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
!!! NEW RELS:[ (exists(S1_1871:exists(v_1869:exists(v_1722:exists(v_1831:exists(S1_1834:exists(S1_1725:exists(S1_1755:exists(v_1752:(S1_1755= | 
  S1_1755=union(S1_1871,{v_1869})) & S1=union(S1_1834,{v_1831}) & 
  S=union(S1_1725,{v_1722}) & v_1722=v_1831 & S1_1755=S1_1834 & 
  S1_1725=union(S1_1755,{v_1752})))))))))) --> DEL(S,S1),
 (exists(S1_1912:exists(v_1910:exists(S1_1783:exists(v_1780:exists(v_1883:exists(S1_1886:(S1_1881= | 
  S1_1881=union(S1_1912,{v_1910})) & S1=union(S1_1886,{v_1883}) & 
  S=union(S1_1783,{v_1780}) & DEL(S_1796,S1_1881) & S1_1783=S_1796 & 
  v_1780=v_1883 & S1_1881=S1_1886))))))) --> DEL(S,S1)]
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
 (exists(S1_2084:exists(v_2082:exists(S1_1969:exists(v_1966:(S1_1969= | 
  S1_1969=union(S1_2084,{v_2082})) & S=union(S1_1969,{v_1966}) & 
  S1_1969=S1 & a=v_1966))))) --> DEL2(a,S,S1),
 (exists(m_1968:exists(n_2006:exists(v_node_220_903':exists(v_node_220_2094:exists(m_2092:exists(m:exists(m_2097:exists(m_2129:exists(n:exists(v_bool_216_905':exists(v_bool_219_904':exists(x:exists(r_2096:exists(res:exists(S1_2130:exists(v_2128:exists(S1_2098:exists(v_2095:exists(S1_1969:exists(v_1966:(S1_2093= & 
  (S1_1969=S_2007 & 1+m_1968=n & 1+n_2006=n & v_node_220_903'=res & 
  v_1966=v_2095 & v_node_220_2094=r_2096 & m_2092=0 & S1_2093=S1_2098 & 
  m=1 & m_2097=0 & !(v_bool_216_905') & (1+a)<=v_2095 & !(v_bool_219_904') & 
  r_2096=null & x!=null & res!=null & 1<=n & DEL2(a,S_2007,S1_2093) | 
  S1_1969=S_2007 & 1+m_1968=n & 1+n_2006=n & v_node_220_903'=res & 
  v_1966=v_2095 & v_node_220_2094=r_2096 & m_2092=0 & S1_2093=S1_2098 & 
  m=1 & m_2097=0 & !(v_bool_216_905') & !(v_bool_219_904') & r_2096=null & 
  (1+v_2095)<=a & x!=null & res!=null & 1<=n & DEL2(a,S_2007,S1_2093)) | 
  (S1_1969=S_2007 & 1+m_1968=n & 1+n_2006=n & v_node_220_903'=res & 
  v_1966=v_2095 & v_node_220_2094=r_2096 & -1+m_2092=m_2129 & 
  S1_2093=S1_2098 & -2+m=m_2129 & -1+m_2097=m_2129 & 0<=m_2129 & (2+
  m_2129)<=n & !(v_bool_216_905') & (1+a)<=v_2095 & !(v_bool_219_904') & 
  x!=null & r_2096!=null & res!=null & DEL2(a,S_2007,S1_2093) | 
  S1_1969=S_2007 & 1+m_1968=n & 1+n_2006=n & v_node_220_903'=res & 
  v_1966=v_2095 & v_node_220_2094=r_2096 & -1+m_2092=m_2129 & 
  S1_2093=S1_2098 & -2+m=m_2129 & -1+m_2097=m_2129 & 0<=m_2129 & (2+
  m_2129)<=n & !(v_bool_216_905') & !(v_bool_219_904') & (1+v_2095)<=a & 
  x!=null & r_2096!=null & res!=null & DEL2(a,S_2007,S1_2093)) & 
  S1_2093=union(S1_2130,{v_2128})) & S1=union(S1_2098,{v_2095}) & 
  S=union(S1_1969,{v_1966})))))))))))))))))))))) --> DEL2(a,S,S1)]
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
!!! NEW RELS:[ (exists(S1_2391:exists(v_2389:exists(S1_2302:exists(v:exists(v_2299:(S1_2302= | 
  S1_2302=union(S1_2391,{v_2389})) & S=union(S1_2302,{v_2299}) & (1+v)<=m & 
  v_2299=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2302:exists(v_2299:v_2299<=v & S1_2302=S_2349 & 
  m_2401=m & (1+v)<=m & FGE(S_2349,m_2401) & S=union(S1_2302,
  {v_2299}))))) --> FGE(S,m)]
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
!!! NEW RELS:[ (exists(S1_2485:exists(v_2483:exists(S1_2443:exists(v_2440:exists(v_2451:exists(S1_2454:(S1_2443= | 
  S1_2443=union(S1_2485,{v_2483})) & S1=union(S1_2454,{v_2451}) & 
  S=union(S1_2443,{v_2440}) & S1_2443=S2 & v_2440=v_2451 & S1_2454= & 
  S1_2454=))))))) --> GN(S,S1,S2)]
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
!!! NEW RELS:[ (exists(S1_2576:exists(v_2574:exists(v_2514:exists(S1_2517:exists(S1_2547:exists(v_2544:(S1_2547= | 
  S1_2547=union(S1_2576,{v_2574})) & S=union(S1_2517,{v_2514}) & 
  S1_2547=S2 & S1_2517=union(S1_2547,{v_2544})))))))) --> GNN(S,S2)]
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
!!! NEW RELS:[ (exists(S1_2691:exists(v_2688:exists(S1_2613:exists(v_2610:exists(S1_2681:exists(v_2678:S1_2691= & 
  S1_2691= & S1_2681=union(S1_2691,{v_2688}) & S1_2681=union(S1_2691,
  {v_2688}) & S1_2613= & v_2610=v_2678 & a=v_2688 & S=union(S1_2613,
  {v_2610}) & S1=union(S1_2681,{v_2678})))))))) --> INS(S,S1,a),
 (exists(S1_2755:exists(v_2753:exists(S1_2613:exists(v_2610:exists(S1_2723:exists(v_2720:S1_2719=union(S1_2755,
  {v_2753}) & S1_2719=S1_2723 & v_2610=v_2720 & S1_2613=S_2645 & 
  INS(S_2645,S1_2719,a) & S=union(S1_2613,{v_2610}) & S1=union(S1_2723,
  {v_2720})))))))) --> INS(S,S1,a)]
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
 (exists(S1_2934:exists(v_2932:exists(S1_2931:exists(v_2929:exists(S1_2798:exists(v_2885:exists(v_2795:exists(S1_2888:exists(S_94:exists(S1_2845:exists(v_2842:(S_2802= & 
  S2_2837= | S2_2837=union(S1_2934,{v_2932}) & S_2802=union(S1_2931,
  {v_2929})) & S2=union(S1_2888,{v_2885}) & S=union(S1_2798,{v_2795}) & 
  CPY(S_2802,S2_2837) & S1_2845=S1_2798 & S_2802=S1_2798 & v_2885=v_2842 & 
  v_2795=v_2842 & S2_2837=S1_2888 & S_94=union(S1_2845,
  {v_2842}))))))))))))) --> CPY(S,S2),
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
 (exists(S1_3207:exists(v_3205:exists(v_3022:exists(S1_3025:exists(Anon_11:exists(v:(S2_3176= | 
  S2_3176=union(S1_3207,{v_3205})) & S=union(S1_3025,{v_3022}) & 
  FIL(S_3079,S2_3176) & S2_3176=S2 & v_3022=v & S1_3025=S_3079 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(m_3024:exists(n_3121:exists(res:exists(v_node_382_727':exists(tmp_90':exists(m_3165:exists(m:exists(m_3218:exists(m_3250:exists(n:exists(v_bool_369_725':exists(v:exists(r_3217:exists(x:exists(v_bool_368_726':exists(S1_3251:exists(v_3249:exists(S1_3219:exists(v_3216:exists(S1_3025:exists(v_3022:(S2_3166= & 
  (S1_3025=S_3122 & 1+m_3024=n & 1+n_3121=n & res=x & v_node_382_727'=x & 
  v_3022=v_3216 & tmp_90'=r_3217 & m_3165=0 & S2_3166=S1_3219 & m=1 & 
  m_3218=0 & (1+v)<=v_3216 & !(v_bool_369_725') & r_3217=null & x!=null & 
  1<=n & FIL(S_3122,S2_3166) & v_bool_368_726' | S1_3025=S_3122 & 1+
  m_3024=n & 1+n_3121=n & res=x & v_node_382_727'=x & v_3022=v_3216 & 
  tmp_90'=r_3217 & m_3165=0 & S2_3166=S1_3219 & m=1 & m_3218=0 & 
  !(v_bool_369_725') & r_3217=null & (1+v_3216)<=v & x!=null & 1<=n & 
  FIL(S_3122,S2_3166) & v_bool_368_726') | (S1_3025=S_3122 & 1+m_3024=n & 1+
  n_3121=n & res=x & v_node_382_727'=x & v_3022=v_3216 & tmp_90'=r_3217 & -1+
  m_3165=m_3250 & S2_3166=S1_3219 & -2+m=m_3250 & -1+m_3218=m_3250 & 
  0<=m_3250 & (2+m_3250)<=n & (1+v)<=v_3216 & !(v_bool_369_725') & 
  r_3217!=null & x!=null & FIL(S_3122,S2_3166) & v_bool_368_726' | 
  S1_3025=S_3122 & 1+m_3024=n & 1+n_3121=n & res=x & v_node_382_727'=x & 
  v_3022=v_3216 & tmp_90'=r_3217 & -1+m_3165=m_3250 & S2_3166=S1_3219 & -2+
  m=m_3250 & -1+m_3218=m_3250 & 0<=m_3250 & (2+m_3250)<=n & 
  !(v_bool_369_725') & (1+v_3216)<=v & r_3217!=null & x!=null & 
  FIL(S_3122,S2_3166) & v_bool_368_726') & S2_3166=union(S1_3251,
  {v_3249})) & S2=union(S1_3219,{v_3216}) & S=union(S1_3025,
  {v_3022}))))))))))))))))))))))) --> FIL(S,S2),
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
 (exists(S1_3841:exists(v_3839:exists(S1_3704:exists(v_3701:exists(Anon_11:exists(v:(S1_3704= | 
  S1_3704=union(S1_3841,{v_3839})) & S=union(S1_3704,{v_3701}) & 
  S1_3704=S2 & v_3701=v & Anon_11=v))))))) --> RMV2(S,S2),
 (exists(m_3703:exists(n_3761:exists(res:exists(v_node_357_750':exists(tmp_91':exists(m_3806:exists(m:exists(m_3848:exists(m_3880:exists(n:exists(v_bool_346_748':exists(v:exists(r_3847:exists(x:exists(v_bool_345_749':exists(S1_3881:exists(v_3879:exists(S1_3849:exists(v_3846:exists(S1_3704:exists(v_3701:(S2_3807= & 
  (S1_3704=S_3762 & 1+m_3703=n & 1+n_3761=n & res=x & v_node_357_750'=x & 
  v_3701=v_3846 & tmp_91'=r_3847 & m_3806=0 & S2_3807=S1_3849 & m=1 & 
  m_3848=0 & (1+v)<=v_3846 & !(v_bool_346_748') & r_3847=null & x!=null & 
  1<=n & RMV2(S_3762,S2_3807) & v_bool_345_749' | S1_3704=S_3762 & 1+
  m_3703=n & 1+n_3761=n & res=x & v_node_357_750'=x & v_3701=v_3846 & 
  tmp_91'=r_3847 & m_3806=0 & S2_3807=S1_3849 & m=1 & m_3848=0 & 
  !(v_bool_346_748') & r_3847=null & (1+v_3846)<=v & x!=null & 1<=n & 
  RMV2(S_3762,S2_3807) & v_bool_345_749') | (S1_3704=S_3762 & 1+m_3703=n & 1+
  n_3761=n & res=x & v_node_357_750'=x & v_3701=v_3846 & tmp_91'=r_3847 & -1+
  m_3806=m_3880 & S2_3807=S1_3849 & -2+m=m_3880 & -1+m_3848=m_3880 & 
  0<=m_3880 & (2+m_3880)<=n & (1+v)<=v_3846 & !(v_bool_346_748') & 
  r_3847!=null & x!=null & RMV2(S_3762,S2_3807) & v_bool_345_749' | 
  S1_3704=S_3762 & 1+m_3703=n & 1+n_3761=n & res=x & v_node_357_750'=x & 
  v_3701=v_3846 & tmp_91'=r_3847 & -1+m_3806=m_3880 & S2_3807=S1_3849 & -2+
  m=m_3880 & -1+m_3848=m_3880 & 0<=m_3880 & (2+m_3880)<=n & 
  !(v_bool_346_748') & (1+v_3846)<=v & r_3847!=null & x!=null & 
  RMV2(S_3762,S2_3807) & v_bool_345_749') & S2_3807=union(S1_3881,
  {v_3879})) & S2=union(S1_3849,{v_3846}) & S=union(S1_3704,
  {v_3701}))))))))))))))))))))))) --> RMV2(S,S2),
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
 (exists(S1_4050:exists(v_4048:exists(S1_3986:exists(v_3983:exists(v_4018:exists(S1_4021:(S2_4017= | 
  S2_4017=union(S1_4050,{v_4048})) & S2=union(S1_4021,{v_4018}) & 
  S1=union(S1_3986,{v_3983}) & TRAV(S1_3990,S2_4017) & S1_3986=S1_3990 & 
  v_3983=v_4018 & S2_4017=S1_4021))))))) --> TRAV(S1,S2),
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
!!! NEW RELS:[ (exists(S1_4142:exists(v_4140:exists(v_4110:exists(S1_4113:(S1_4113= | 
  S1_4113=union(S1_4142,{v_4140})) & S1=union(S1_4113,{v_4110}) & 
  S1_4113=S2))))) --> PF(S1,S2)]
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
                              tmp_130_4182'=x' & v=v_4156_4186 & 
                              x=r_4157_4183 & S=S1_4159_4185 & 
                              flted_90_129=1+m_4158_4184 & n=m_4158_4184 & 
                              S1=union(S1_4159_4185,{v_4156_4186}) & 0<=n&
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
!!! NEW RELS:[ (exists(S1_4432:exists(v_4430:exists(v_4315:exists(S1_4318:exists(S1_4286:exists(v_4283:S2_4301=union(S1_4318,
  {v_4315}) & S_4395=union(S1_4432,{v_4430}) & v_4283=v_4315 & 
  S1_4286=S1_4299 & S2=S1_4318 & S_4395=S & REV(S_4395,S1_4299,S2_4301) & 
  S1=union(S1_4286,{v_4283})))))))) --> REV(S,S1,S2),
 (exists(S1_4478:exists(v_4476:(S2= | S2=union(S1_4478,{v_4476})) & S1= & 
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
                              v=v_4504_4546 & y=r_4505_4543 & 
                              S=S1_4507_4545 & k=1+m_4506_4544 & 
                              j=m_4506_4544 & x'!=null & 0<=m_4506_4544 & 
                              S2=union(S1_4507_4545,{v_4504_4546}) & 
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
!!! NEW RELS:[ (exists(S1_5038:exists(v_5036:(S2= | S2=union(S1_5038,{v_5036})) & S1= & 
  S2=S))) --> SPI(S,S1,S2),
 (exists(S1_5117:exists(v_5115:exists(S1_4891:exists(S1_4926:exists(v_4888:exists(v_5054:exists(v_4923:exists(S1_5057:exists(S1_5067:exists(v_5064:(S_5004= | 
  S_5004=union(S1_5117,{v_5115})) & S=union(S1_5057,{v_5054}) & 
  S1=union(S1_4891,{v_4888}) & S2=union(S1_4926,{v_4923}) & 
  SPI(S_5004,S1_4933,S2_4935) & S1_4891=S1_4933 & S1_4926=S2_4935 & 
  v_4888=v_5054 & v_4923=v_5064 & S_5004=S1_5067 & S1_5057=union(S1_5067,
  {v_5064}) & S1_5057=union(S1_5067,{v_5064})))))))))))) --> SPI(S,S1,S2),
 (exists(S1_5162_5165:exists(v_5163:S1=S & S2= & S1=union(S1_5162_5165,
  {v_5163})))) --> SPI(S,S1,S2)]
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
!!! NEW RELS:[ (exists(S1_5350:exists(v_5348:exists(S1_5227:exists(v_5224:exists(S1_5321:exists(v_5318:S1_5321= & 
  S1_5321= & S1_5227=union(S1_5350,{v_5348}) & v_5224=v_5318 & S1_5227=S2 & 
  S=union(S1_5227,{v_5224}) & S1=union(S1_5321,
  {v_5318})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_5453:exists(v_5451:exists(S1_5456:exists(v_5454:exists(S1_5267:exists(v_5264:exists(S1_5370:exists(v_5367:S1_5363=union(S1_5453,
  {v_5451}) & S2_5364=union(S1_5456,{v_5454}) & S1_5363=S1_5370 & 
  v_5264=v_5367 & S1_5267=S_5269 & S2_5364=S2 & 
  SPLIT(S_5269,S1_5363,S2_5364) & S=union(S1_5267,{v_5264}) & 
  S1=union(S1_5370,{v_5367})))))))))) --> SPLIT(S,S1,S2)]
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

Total verification time: 24.02 second(s)
	Time spent in main process: 2.54 second(s)
	Time spent in child processes: 21.48 second(s)
