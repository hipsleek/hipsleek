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
                              EAssume 24::
                                EXISTS(m,S: x::ll2<m,S>@M[Orig][LHSCase]&
                                m=n2+n1 & APP(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase] * 
                  y::ll2<n2,S2>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 24::
                              x::ll2<m,S>@M[Orig][LHSCase]&m=n2+n1 & 
                              union(S1,S2)=S & 0<=n1 & 0<=n2&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1441:exists(v_1439:exists(S1_1407:exists(v_1309:exists(v_1404:exists(S1_1312:(S2= | 
  S2=union(S1_1441,{v_1439})) & S=union(S1_1407,{v_1404}) & S1=union(S1_1312,
  {v_1309}) & S2=S1_1407 & v_1309=v_1404 & S1_1312=))))))) --> APP(S,S1,S2),
 (exists(S1_1501:exists(v_1499:exists(S1_1312:exists(v_1309:exists(S1_1469:exists(v_1466:S_1465=union(S1_1501,
  {v_1499}) & S_1465=S1_1469 & v_1309=v_1466 & S1_1312=S1_1351 & 
  S2=S2_1353 & APP(S_1465,S1_1351,S2_1353) & S1=union(S1_1312,{v_1309}) & 
  S=union(S1_1469,{v_1466})))))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! REL :  ASS(S1,v)
!!! POST:  S1= | S1={v}
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ASS]
              EBase exists (Expl)(Impl)[m; 
                    S](ex)x::ll2<m,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::ref [x]
                                EXISTS(n_131,
                                S1: x'::ll2<n_131,S1>@M[Orig][LHSCase]&
                                ASS(S1,v) & n_131=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; S](ex)x::ll2<m,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 17::ref [x]
                              x'::ll2<n_131,S1>@M[Orig][LHSCase]&n_131=n & 
                              (S1= | S1={v}) & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S1=) --> ASS(S1,v),
 (exists(S_1677:exists(S1_1717:exists(v_1715:S_1677={v} & S_1677=S1 & 
  S_1677=union(S1_1717,{v_1715}))))) --> ASS(S1,v)]
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
                              EAssume 42::
                                EXISTS(m,S1: x::ll2<m,S1>@M[Orig][LHSCase]&
                                DEL(S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              x::ll2<m,S1>@M[Orig][LHSCase]&S1<subset> S  & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_1912:exists(v_1910:exists(v_1763:exists(v_1872:exists(S1_1875:exists(S1_1766:exists(S1_1796:exists(v_1793:(S1_1796= | 
  S1_1796=union(S1_1912,{v_1910})) & S1=union(S1_1875,{v_1872}) & 
  S=union(S1_1766,{v_1763}) & v_1763=v_1872 & S1_1796=S1_1875 & 
  S1_1766=union(S1_1796,{v_1793})))))))))) --> DEL(S,S1),
 (exists(S1_1953:exists(v_1951:exists(S1_1824:exists(v_1821:exists(v_1924:exists(S1_1927:(S1_1922= | 
  S1_1922=union(S1_1953,{v_1951})) & S1=union(S1_1927,{v_1924}) & 
  S=union(S1_1824,{v_1821}) & DEL(S_1837,S1_1922) & S1_1824=S_1837 & 
  v_1821=v_1924 & S1_1922=S1_1927))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  a <notin> S  | a <in> S 
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 46::
                                EXISTS(m,S1: res::ll2<m,S1>@M[Orig][LHSCase]&
                                m<=n & DEL2(a,S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&(a <notin> S  | a <in> S ) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 46::
                              res::ll2<m,S1>@M[Orig][LHSCase]&m<=n & (S1=S & 
                              a <notin> S  | S1<subset> S  & a <in> S ) & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S1= & S= & S1=S) --> DEL2(a,S,S1),
 (S1=S & S= & S1=) --> DEL2(a,S,S1),
 (exists(S1_2125:exists(v_2123:exists(S1_2010:exists(v_2007:(S1_2010= | 
  S1_2010=union(S1_2125,{v_2123})) & S=union(S1_2010,{v_2007}) & 
  S1_2010=S1 & a=v_2007))))) --> DEL2(a,S,S1),
 (exists(m_2009:exists(n_2047:exists(v_node_234_919':exists(v_node_234_2135:exists(m_2133:exists(m:exists(m_2138:exists(m_2170:exists(n:exists(v_bool_230_921':exists(v_bool_233_920':exists(x:exists(r_2137:exists(res:exists(S1_2171:exists(v_2169:exists(S1_2139:exists(v_2136:exists(S1_2010:exists(v_2007:(S1_2134= & 
  (S1_2010=S_2048 & 1+m_2009=n & 1+n_2047=n & v_node_234_919'=res & 
  v_2007=v_2136 & v_node_234_2135=r_2137 & m_2133=0 & S1_2134=S1_2139 & 
  m=1 & m_2138=0 & !(v_bool_230_921') & (1+a)<=v_2136 & !(v_bool_233_920') & 
  r_2137=null & x!=null & res!=null & 1<=n & DEL2(a,S_2048,S1_2134) | 
  S1_2010=S_2048 & 1+m_2009=n & 1+n_2047=n & v_node_234_919'=res & 
  v_2007=v_2136 & v_node_234_2135=r_2137 & m_2133=0 & S1_2134=S1_2139 & 
  m=1 & m_2138=0 & !(v_bool_230_921') & !(v_bool_233_920') & r_2137=null & 
  (1+v_2136)<=a & x!=null & res!=null & 1<=n & DEL2(a,S_2048,S1_2134)) | 
  (S1_2010=S_2048 & 1+m_2009=n & 1+n_2047=n & v_node_234_919'=res & 
  v_2007=v_2136 & v_node_234_2135=r_2137 & -1+m_2133=m_2170 & 
  S1_2134=S1_2139 & -2+m=m_2170 & -1+m_2138=m_2170 & 0<=m_2170 & (2+
  m_2170)<=n & !(v_bool_230_921') & (1+a)<=v_2136 & !(v_bool_233_920') & 
  x!=null & r_2137!=null & res!=null & DEL2(a,S_2048,S1_2134) | 
  S1_2010=S_2048 & 1+m_2009=n & 1+n_2047=n & v_node_234_919'=res & 
  v_2007=v_2136 & v_node_234_2135=r_2137 & -1+m_2133=m_2170 & 
  S1_2134=S1_2139 & -2+m=m_2170 & -1+m_2138=m_2170 & 0<=m_2170 & (2+
  m_2170)<=n & !(v_bool_230_921') & !(v_bool_233_920') & (1+v_2136)<=a & 
  x!=null & r_2137!=null & res!=null & DEL2(a,S_2048,S1_2134)) & 
  S1_2134=union(S1_2171,{v_2169})) & S1=union(S1_2139,{v_2136}) & 
  S=union(S1_2010,{v_2007})))))))))))))))))))))) --> DEL2(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              EAssume 94::
                                
                                true&res=null&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_22,
                                   m: res::node<m,Anon_22>@M[Orig]&v<m & 
                                   FGE(S,m)&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 94::
                              
                              true&res=null & 0<=n&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_22>@M[Orig]&v<m & 
                                 {m}<subset> S  & 0<=n&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(S1_2444:exists(v_2442:exists(S1_2355:exists(v:exists(v_2352:(S1_2355= | 
  S1_2355=union(S1_2444,{v_2442})) & S=union(S1_2355,{v_2352}) & (1+v)<=m & 
  v_2352=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2355:exists(v_2352:v_2352<=v & S1_2355=S_2402 & 
  m_2454=m & (1+v)<=m & FGE(S_2402,m_2454) & S=union(S1_2355,
  {v_2352}))))) --> FGE(S,m)]
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
                              EAssume 28::ref [x]
                                EXISTS(flted_146_121,flted_146_122,S1,
                                S2: x'::ll2<flted_146_122,S1>@M[Orig][LHSCase] * 
                                res::ll2<flted_146_121,S2>@M[Orig][LHSCase]&
                                flted_146_122=1 & flted_146_121+1=n & 
                                GN(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              x'::ll2<flted_146_122,S1>@M[Orig][LHSCase] * 
                              res::ll2<flted_146_121,S2>@M[Orig][LHSCase]&
                              flted_146_122=1 & flted_146_121+1=n & union(S1,
                              S2)=S & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2538:exists(v_2536:exists(S1_2496:exists(v_2493:exists(v_2504:exists(S1_2507:(S1_2496= | 
  S1_2496=union(S1_2538,{v_2536})) & S1=union(S1_2507,{v_2504}) & 
  S=union(S1_2496,{v_2493}) & S1_2496=S2 & v_2493=v_2504 & S1_2507= & 
  S1_2507=))))))) --> GN(S,S1,S2)]
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
                              EAssume 38::
                                EXISTS(flted_187_114,
                                S2: res::ll2<flted_187_114,S2>@M[Orig][LHSCase]&
                                flted_187_114+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  2<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              res::ll2<flted_187_114,S2>@M[Orig][LHSCase]&
                              flted_187_114+2=n & S2<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2629:exists(v_2627:exists(v_2567:exists(S1_2570:exists(S1_2600:exists(v_2597:(S1_2600= | 
  S1_2600=union(S1_2629,{v_2627})) & S=union(S1_2570,{v_2567}) & 
  S1_2600=S2 & S1_2570=union(S1_2600,{v_2597})))))))) --> GNN(S,S2)]
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
                              EAssume 39::
                                EXISTS(flted_198_111,
                                S1: x::ll2<flted_198_111,S1>@M[Orig][LHSCase]&
                                flted_198_111=1+n & INS(S,S1,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              x::ll2<flted_198_111,S1>@M[Orig][LHSCase]&
                              flted_198_111=1+n & S1=union(S,{a}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2744:exists(v_2741:exists(S1_2666:exists(v_2663:exists(S1_2734:exists(v_2731:S1_2744= & 
  S1_2744= & S1_2734=union(S1_2744,{v_2741}) & S1_2734=union(S1_2744,
  {v_2741}) & S1_2666= & v_2663=v_2731 & a=v_2741 & S=union(S1_2666,
  {v_2663}) & S1=union(S1_2734,{v_2731})))))))) --> INS(S,S1,a),
 (exists(S1_2808:exists(v_2806:exists(S1_2666:exists(v_2663:exists(S1_2776:exists(v_2773:S1_2772=union(S1_2808,
  {v_2806}) & S1_2772=S1_2776 & v_2663=v_2773 & S1_2666=S_2698 & 
  INS(S_2698,S1_2772,a) & S=union(S1_2666,{v_2663}) & S1=union(S1_2776,
  {v_2773})))))))) --> INS(S,S1,a)]
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
                              EAssume 72::
                                EXISTS(n_93,S_94,n_95,
                                S2: x::ll2<n_93,S_94>@M[Orig][LHSCase] * 
                                res::ll2<n_95,S2>@M[Orig][LHSCase]&
                                CPY(S,S2) & n_93=n & S_94=S & n_95=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              x::ll2<n_93,S_94>@M[Orig][LHSCase] * 
                              res::ll2<n_95,S2>@M[Orig][LHSCase]&n_93=n & 
                              S_94=S & n_95=n & S2=S & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S_94:S2= & S= & S_94=S & S_94= & S_94=)) --> CPY(S,S2),
 (exists(S1_2987:exists(v_2985:exists(S1_2984:exists(v_2982:exists(S1_2851:exists(v_2938:exists(v_2848:exists(S1_2941:exists(S_94:exists(S1_2898:exists(v_2895:(S_2855= & 
  S2_2890= | S2_2890=union(S1_2987,{v_2985}) & S_2855=union(S1_2984,
  {v_2982})) & S2=union(S1_2941,{v_2938}) & S=union(S1_2851,{v_2848}) & 
  CPY(S_2855,S2_2890) & S1_2898=S1_2851 & S_2855=S1_2851 & v_2938=v_2895 & 
  v_2848=v_2895 & S2_2890=S1_2941 & S_94=union(S1_2898,
  {v_2895}))))))))))))) --> CPY(S,S2),
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
                              EAssume 86::
                                EXISTS(m,S2: res::ll2<m,S2>@M[Orig][LHSCase]&
                                m<=n & FIL(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 86::
                              res::ll2<m,S2>@M[Orig][LHSCase]&m<=n & 
                              S2<subset> S  & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S= & S2=S) --> FIL(S,S2),
 (exists(S1_3260:exists(v_3258:exists(v_3075:exists(S1_3078:exists(Anon_11:exists(v:(S2_3229= | 
  S2_3229=union(S1_3260,{v_3258})) & S=union(S1_3078,{v_3075}) & 
  FIL(S_3132,S2_3229) & S2_3229=S2 & v_3075=v & S1_3078=S_3132 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(m_3077:exists(n_3174:exists(res:exists(v_node_397_741':exists(tmp_90':exists(m_3218:exists(m:exists(m_3271:exists(m_3303:exists(n:exists(v_bool_385_739':exists(v:exists(r_3270:exists(x:exists(v_bool_384_740':exists(S1_3304:exists(v_3302:exists(S1_3272:exists(v_3269:exists(S1_3078:exists(v_3075:(S2_3219= & 
  (S1_3078=S_3175 & 1+m_3077=n & 1+n_3174=n & res=x & v_node_397_741'=x & 
  v_3075=v_3269 & tmp_90'=r_3270 & m_3218=0 & S2_3219=S1_3272 & m=1 & 
  m_3271=0 & (1+v)<=v_3269 & !(v_bool_385_739') & r_3270=null & x!=null & 
  1<=n & FIL(S_3175,S2_3219) & v_bool_384_740' | S1_3078=S_3175 & 1+
  m_3077=n & 1+n_3174=n & res=x & v_node_397_741'=x & v_3075=v_3269 & 
  tmp_90'=r_3270 & m_3218=0 & S2_3219=S1_3272 & m=1 & m_3271=0 & 
  !(v_bool_385_739') & r_3270=null & (1+v_3269)<=v & x!=null & 1<=n & 
  FIL(S_3175,S2_3219) & v_bool_384_740') | (S1_3078=S_3175 & 1+m_3077=n & 1+
  n_3174=n & res=x & v_node_397_741'=x & v_3075=v_3269 & tmp_90'=r_3270 & -1+
  m_3218=m_3303 & S2_3219=S1_3272 & -2+m=m_3303 & -1+m_3271=m_3303 & 
  0<=m_3303 & (2+m_3303)<=n & (1+v)<=v_3269 & !(v_bool_385_739') & 
  r_3270!=null & x!=null & FIL(S_3175,S2_3219) & v_bool_384_740' | 
  S1_3078=S_3175 & 1+m_3077=n & 1+n_3174=n & res=x & v_node_397_741'=x & 
  v_3075=v_3269 & tmp_90'=r_3270 & -1+m_3218=m_3303 & S2_3219=S1_3272 & -2+
  m=m_3303 & -1+m_3271=m_3303 & 0<=m_3303 & (2+m_3303)<=n & 
  !(v_bool_385_739') & (1+v_3269)<=v & r_3270!=null & x!=null & 
  FIL(S_3175,S2_3219) & v_bool_384_740') & S2_3219=union(S1_3304,
  {v_3302})) & S2=union(S1_3272,{v_3269}) & S=union(S1_3078,
  {v_3075}))))))))))))))))))))))) --> FIL(S,S2),
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
                              EAssume 79::
                                EXISTS(m,S2: res::ll2<m,S2>@M[Orig][LHSCase]&
                                m<=n & RMV2(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 79::
                              res::ll2<m,S2>@M[Orig][LHSCase]&m<=n & 
                              S2<subset> S  & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S= & S2=S) --> RMV2(S,S2),
 (exists(S1_3894:exists(v_3892:exists(S1_3757:exists(v_3754:exists(Anon_11:exists(v:(S1_3757= | 
  S1_3757=union(S1_3894,{v_3892})) & S=union(S1_3757,{v_3754}) & 
  S1_3757=S2 & v_3754=v & Anon_11=v))))))) --> RMV2(S,S2),
 (exists(m_3756:exists(n_3814:exists(res:exists(v_node_373_764':exists(tmp_91':exists(m_3859:exists(m:exists(m_3901:exists(m_3933:exists(n:exists(v_bool_362_762':exists(v:exists(r_3900:exists(x:exists(v_bool_361_763':exists(S1_3934:exists(v_3932:exists(S1_3902:exists(v_3899:exists(S1_3757:exists(v_3754:(S2_3860= & 
  (S1_3757=S_3815 & 1+m_3756=n & 1+n_3814=n & res=x & v_node_373_764'=x & 
  v_3754=v_3899 & tmp_91'=r_3900 & m_3859=0 & S2_3860=S1_3902 & m=1 & 
  m_3901=0 & (1+v)<=v_3899 & !(v_bool_362_762') & r_3900=null & x!=null & 
  1<=n & RMV2(S_3815,S2_3860) & v_bool_361_763' | S1_3757=S_3815 & 1+
  m_3756=n & 1+n_3814=n & res=x & v_node_373_764'=x & v_3754=v_3899 & 
  tmp_91'=r_3900 & m_3859=0 & S2_3860=S1_3902 & m=1 & m_3901=0 & 
  !(v_bool_362_762') & r_3900=null & (1+v_3899)<=v & x!=null & 1<=n & 
  RMV2(S_3815,S2_3860) & v_bool_361_763') | (S1_3757=S_3815 & 1+m_3756=n & 1+
  n_3814=n & res=x & v_node_373_764'=x & v_3754=v_3899 & tmp_91'=r_3900 & -1+
  m_3859=m_3933 & S2_3860=S1_3902 & -2+m=m_3933 & -1+m_3901=m_3933 & 
  0<=m_3933 & (2+m_3933)<=n & (1+v)<=v_3899 & !(v_bool_362_762') & 
  r_3900!=null & x!=null & RMV2(S_3815,S2_3860) & v_bool_361_763' | 
  S1_3757=S_3815 & 1+m_3756=n & 1+n_3814=n & res=x & v_node_373_764'=x & 
  v_3754=v_3899 & tmp_91'=r_3900 & -1+m_3859=m_3933 & S2_3860=S1_3902 & -2+
  m=m_3933 & -1+m_3901=m_3933 & 0<=m_3933 & (2+m_3933)<=n & 
  !(v_bool_362_762') & (1+v_3899)<=v & r_3900!=null & x!=null & 
  RMV2(S_3815,S2_3860) & v_bool_361_763') & S2_3860=union(S1_3934,
  {v_3932})) & S2=union(S1_3902,{v_3899}) & S=union(S1_3757,
  {v_3754}))))))))))))))))))))))) --> RMV2(S,S2),
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
                              EAssume 69::
                                EXISTS(n_97,
                                S2: x::ll2<n_97,S2>@M[Orig][LHSCase]&
                                TRAV(S1,S2) & n_97=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 69::
                              x::ll2<n_97,S2>@M[Orig][LHSCase]&n_97=n & 
                              S1=S2 & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S1= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_4103:exists(v_4101:exists(S1_4039:exists(v_4036:exists(v_4071:exists(S1_4074:(S2_4070= | 
  S2_4070=union(S1_4103,{v_4101})) & S2=union(S1_4074,{v_4071}) & 
  S1=union(S1_4039,{v_4036}) & TRAV(S1_4043,S2_4070) & S1_4039=S1_4043 & 
  v_4036=v_4071 & S2_4070=S1_4074))))))) --> TRAV(S1,S2),
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
                              EAssume 21::ref [x]
                                EXISTS(flted_107_126,
                                S2: x'::ll2<flted_107_126,S2>@M[Orig][LHSCase]&
                                flted_107_126+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 21::ref [x]
                              x'::ll2<flted_107_126,S2>@M[Orig][LHSCase]&
                              flted_107_126+1=m & S2<subset> S1  & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4195:exists(v_4193:exists(v_4163:exists(S1_4166:(S1_4166= | 
  S1_4166=union(S1_4195,{v_4193})) & S1=union(S1_4166,{v_4163}) & 
  S1_4166=S2))))) --> PF(S1,S2)]
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
                              EAssume 19::ref [x]
                                EXISTS(flted_96_129,
                                S1: x'::ll2<flted_96_129,S1>@M[Orig][LHSCase]&
                                flted_96_129=1+n & PUF(S1,S,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 19::ref [x]
                              x'::ll2<flted_96_129,S1>@M[Orig][LHSCase]&
                              flted_96_129=1+n & S1=union(S,{v}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4237:exists(v_4235:exists(S1_4212:exists(v_4209:(S= | 
  S=union(S1_4237,{v_4235})) & S1=union(S1_4212,{v_4209}) & S=S1_4212 & 
  v=v_4209))))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! REL :  RF(S1,S2)
!!! POST:  S2=S1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RF]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::
                                EXISTS(n_124,
                                S2: x::ll2<n_124,S2>@M[Orig][LHSCase]&
                                RF(S1,S2) & n_124=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 27::
                              x::ll2<n_124,S2>@M[Orig][LHSCase]&n_124=n & 
                              S2=S1 & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4263_4266:exists(v_4264:(S1= | S1=union(S1_4263_4266,
  {v_4264})) & S1=S2))) --> RF(S1,S2)]
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
                              EAssume 56::ref [xs;ys]
                                EXISTS(flted_267_106,
                                S: ys'::ll2<flted_267_106,S>@M[Orig][LHSCase]&
                                flted_267_106=m+n & xs'=null & REV(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                  ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 56::ref [xs;ys]
                              ys'::ll2<flted_267_106,S>@M[Orig][LHSCase]&
                              flted_267_106=m+n & xs'=null & S=union(S1,
                              S2) & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4494:exists(v_4492:exists(v_4377:exists(S1_4380:exists(S1_4348:exists(v_4345:S2_4363=union(S1_4380,
  {v_4377}) & S_4457=union(S1_4494,{v_4492}) & v_4345=v_4377 & 
  S1_4348=S1_4361 & S2=S1_4380 & S_4457=S & REV(S_4457,S1_4361,S2_4363) & 
  S1=union(S1_4348,{v_4345})))))))) --> REV(S,S1,S2),
 (exists(S1_4540:exists(v_4538:(S2= | S2=union(S1_4540,{v_4538})) & S1= & 
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
                              EAssume 30::ref [x]
                                EXISTS(k,S2: x::ll2<k,S2>@M[Orig][LHSCase]&
                                1<=k & k=1+j & SN(S,S2,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig] * 
                  t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                  y::ll2<j,S>@M[Orig][LHSCase]&x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 30::ref [x]
                              x::ll2<k,S2>@M[Orig][LHSCase]&1<=k & k=1+j & 
                              S2=union(S,{v}) & 0<=Anon_16 & 0<=j&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4603:exists(v_4601:exists(S1_4569:exists(v_4566:(S= | 
  S=union(S1_4603,{v_4601}) | S= | S=union(S1_4603,{v_4601})) & 
  S2=union(S1_4569,{v_4566}) & S=S1_4569 & v=v_4566))))) --> SN(S,S2,v)]
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
                              EAssume 62::ref [x]
                                EXISTS(n2,n1,S1,
                                S2: x'::ll2<n1,S1>@M[Orig][LHSCase] * 
                                res::ll2<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                                0<n1 & 0<n2 & n1=a & SPLIT(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 62::ref [x]
                              x'::ll2<n1,S1>@M[Orig][LHSCase] * 
                              res::ll2<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                              0<n1 & 0<n2 & n1=a & union(S1,S2)=S & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5407:exists(v_5405:exists(S1_5284:exists(v_5281:exists(S1_5378:exists(v_5375:S1_5378= & 
  S1_5378= & S1_5284=union(S1_5407,{v_5405}) & v_5281=v_5375 & S1_5284=S2 & 
  S=union(S1_5284,{v_5281}) & S1=union(S1_5378,
  {v_5375})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_5510:exists(v_5508:exists(S1_5513:exists(v_5511:exists(S1_5324:exists(v_5321:exists(S1_5427:exists(v_5424:S1_5420=union(S1_5510,
  {v_5508}) & S2_5421=union(S1_5513,{v_5511}) & S1_5420=S1_5427 & 
  v_5321=v_5424 & S1_5324=S_5326 & S2_5421=S2 & 
  SPLIT(S_5326,S1_5420,S2_5421) & S=union(S1_5324,{v_5321}) & 
  S1=union(S1_5427,{v_5424})))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! REL :  SWAP(S1,S2,S3,S4)
!!! POST:  S1= & S2=S3 & S4=
!!! PRE :  S1=
!!! OLD SPECS: ((None,[]),EInfer [SWAP]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]&0<=n & 0<=m&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::ref [x;y]
                                EXISTS(m_132,n_133,S3,
                                S4: x'::ll2<m_132,S3>@M[Orig][LHSCase] * 
                                y'::ll2<n_133,S4>@M[Orig][LHSCase]&
                                SWAP(S1,S2,S3,S4) & m_132=m & n_133=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]&0<=n & 0<=m&
                  {FLOW,(20,21)=__norm}
                    EBase true&S1= & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 14::ref [x;y]
                              x'::ll2<m_132,S3>@M[Orig][LHSCase] * 
                              y'::ll2<n_133,S4>@M[Orig][LHSCase]&m_132=m & 
                              n_133=n & S1= & S2=S3 & S4= & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5610_5617:exists(v_5615:exists(S1_5614:exists(v_5612:(S1= & 
  S2= | S1=union(S1_5610_5617,{v_5615}) & S2=union(S1_5614,{v_5612}) | 
  S1=union(S1_5610_5617,{v_5615}) & S2= | S2=union(S1_5614,{v_5612}) & 
  S1=) & S1=S4 & S2=S3))))) --> SWAP(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (171,13)  (171,4)  (35,17)  (35,24)  (36,7)  (36,14)  (252,4)  (252,11)  (257,4)  (257,11)  (256,10)  (256,4)  (255,9)  (255,13)  (255,4)  (255,4) )

Total verification time: 17.75 second(s)
	Time spent in main process: 2.92 second(s)
	Time spent in child processes: 14.83 second(s)
