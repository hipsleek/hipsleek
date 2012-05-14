/usr/local/bin/mona

Processing file "sll_msob.ss"
Parsing sll_msob.ss ...
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

Checking procedure create_list$int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
!!! REL :  DEL(S1,S)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; xs; xl; 
                    S](ex)x::sll1<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{333}]&
                    (([1<=a & (1+a)<=n][xs<=xl][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(nres,sres,lres,
                                S1: x::sll1<nres,sres,lres,S1>@M[Orig][LHSCase]@ rem br[{334,333}]&
                                (
                                ([1+nres=n][sres<=lres & lres<=xl & xs<=sres]
                                 [DEL(S1,S)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; xl; 
                  S](ex)x::sll1<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{333}]&(
                  ([S!=()][x!=null][xs<=xl][1<=a & (1+a)<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(nres_1906,sres_1907,lres_1908,
                              S1_1909: x::sll1<nres_1906,sres_1907,lres_1908,S1_1909>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([sres_1907<=lres_1908 & xs<=xl & 
                                 xs<=sres_1907 & lres_1908<=xl]
                               [1+nres_1906=n & 0<=n][S1_1909<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(xs:exists(xl:exists(ql_1653:exists(ql_1698:exists(qmin_1699:exists(lres:exists(qs_1697:exists(qs_1652:exists(sres:exists(S1_1701:exists(S1_1800:exists(qmin_1798:exists(S1_1656:exists(qmin_1654:xs=sres & 
  xl=lres & ql_1653=lres & ql_1698=lres & qmin_1699=qs_1652 & 
  S1_1656=union(S1_1701,{qmin_1699}) & S1_1656!=() & qs_1697<=lres & 
  qs_1652<=qs_1697 & sres<=qs_1652 & qmin_1654=sres & qmin_1798=sres & 
  S1_1701=S1_1800 & S1=union(S1_1800,{qmin_1798}) & S=union(S1_1656,
  {qmin_1654}) & S!=()))))))))))))))) --> DEL(S1,S),
 (exists(lres_1846:exists(xl_1759:exists(xl:exists(qs_1741:exists(ql_1742:exists(lres:exists(sres_1845:exists(xs_1758:exists(xs:exists(sres:exists(S1_1851:exists(qmin_1849:exists(S1_1745:exists(qmin_1743:lres_1846=lres & 
  xl_1759=ql_1742 & xl=ql_1742 & qs_1741=xs_1758 & S1_1847!=() & 
  S1_1745!=() & lres<=ql_1742 & sres_1845<=lres & xs_1758<=sres_1845 & 
  sres<=xs_1758 & qmin_1743=sres & xs=sres & qmin_1849=sres & 
  S1_1745=S_1760 & S1_1847=S1_1851 & DEL(S1_1847,S_1760) & S!=() & 
  S1=union(S1_1851,{qmin_1849}) & S=union(S1_1745,
  {qmin_1743})))))))))))))))) --> DEL(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL2(S1,S,v)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; xs; xl; 
                    S](ex)x::sll1<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{334,333}]&
                    (([true][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(nres,sres,lres,
                                S1: res::sll1<nres,sres,lres,S1>@M[Orig][LHSCase]@ rem br[{334,333}]&
                                (
                                ([nres<=n & (-1+n)<=nres]
                                 [sres<=lres & lres<=xl & xs<=sres]
                                 [DEL2(S1,S,v)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; xl; 
                  S](ex)x::sll1<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{334,333}]&
                  (([xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              EXISTS(nres_2188,sres_2189,lres_2190,
                              S1_2191: res::sll1<nres_2188,sres_2189,lres_2190,S1_2191>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([sres_2189<=lres_2190 & xs<=xl & 
                                 xs<=sres_2189 & lres_2190<=xl]
                               [nres_2188<=n & 0<=n & (-1+n)<=nres_2188]
                               [S1_2191<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(q_1945:exists(q_2043:exists(res:exists(xs:exists(xl:exists(n:exists(sres:exists(lres:exists(v_node_280_890':exists(flted_15_1941:exists(qs_1942:exists(ql_1943:exists(x:exists(v_bool_278_914':exists(nres:exists(v_bool_279_904':exists(S1_2044:exists(qmin_2042:exists(S1_1946:exists(qmin_1944:(q_1945=q_2043 & 
  res=x & S1_2044=S1_1946 & qmin_1944=qmin_2042 & xs=qmin_2042 & 
  xl=ql_1943 & n=nres & sres=qmin_2042 & lres=ql_1943 & v_node_280_890'=x & 
  1+flted_15_1941=nres & (1+v)<=qmin_2042 & qmin_2042<=qs_1942 & 
  qs_1942<=ql_1943 & nres<=-1 & x!=null & 1<=v_bool_278_914' & 
  1<=v_bool_279_904' | q_1945=q_2043 & res=x & S1_2044=S1_1946 & 
  qmin_1944=qmin_2042 & xs=qmin_2042 & xl=ql_1943 & n=nres & 
  sres=qmin_2042 & lres=ql_1943 & v_node_280_890'=x & 1+flted_15_1941=nres & 
  (1+v)<=qmin_2042 & qmin_2042<=qs_1942 & qs_1942<=ql_1943 & x!=null & 
  1<=v_bool_278_914' & 1<=nres & 1<=v_bool_279_904') & S1=union(S1_2044,
  {qmin_2042}) & S=union(S1_1946,{qmin_1944}) & 
  S!=()))))))))))))))))))))) --> DEL2(S1,S,v),
 (exists(xs:exists(xl:exists(n:exists(q_1945:exists(res:exists(v_node_283_896':exists(sres:exists(lres:exists(nres:exists(qs_1942:exists(ql_1943:exists(v_bool_279_904':exists(x:exists(v_bool_278_914':exists(v_bool_282_903':exists(flted_15_1941:exists(S1_1946:exists(qmin_1944:(S1=S1_1946 & 
  xs=v & xl=ql_1943 & -1+n=flted_15_1941 & q_1945=v_node_283_896' & 
  res=v_node_283_896' & qmin_1944=v & sres=qs_1942 & lres=ql_1943 & 
  nres=flted_15_1941 & v<=qs_1942 & qs_1942<=ql_1943 & v_bool_279_904'<=0 & 
  flted_15_1941<=-2 & x!=null & 1<=v_bool_278_914' & 1<=v_bool_282_903' | 
  S1=S1_1946 & xs=v & xl=ql_1943 & -1+n=flted_15_1941 & 
  q_1945=v_node_283_896' & res=v_node_283_896' & qmin_1944=v & 
  sres=qs_1942 & lres=ql_1943 & nres=flted_15_1941 & v<=qs_1942 & 
  qs_1942<=ql_1943 & v_bool_279_904'<=0 & x!=null & 1<=v_bool_278_914' & 
  1<=v_bool_282_903' & 0<=flted_15_1941) & S=union(S1_1946,{qmin_1944}) & 
  S!=()))))))))))))))))))) --> DEL2(S1,S,v),
 (exists(lres_2030:exists(ql_1943:exists(xs_1986:exists(xl:exists(xl_1987:exists(lres:exists(sres_2029:exists(qs_1942:exists(xs:exists(sres:exists(S1_2100:exists(qmin_2098:exists(S1_1946:exists(qmin_1944:lres_2030=lres & 
  ql_1943=xl_1987 & xs_1986=qs_1942 & xl=xl_1987 & lres<=xl_1987 & 
  sres_2029<=lres & qs_1942<=sres_2029 & sres<=qs_1942 & xs=sres & 
  qmin_1944=sres & qmin_2098=sres & S1_1946=S_1988 & S1_2031=S1_2100 & (1+
  sres)<=v & DEL2(S1_2031,S_1988,v) & S1=union(S1_2100,{qmin_2098}) & 
  S=union(S1_1946,{qmin_1944}) & S!=()))))))))))))))) --> DEL2(S1,S,v),
 (S1= & S=) --> DEL2(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; sm; sl; 
                    S](ex)x::sll2<n,sm,sl,S>@M[Orig][LHSCase]@ rem br[{332,331}]&
                    (([true][sm<=sl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 79::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(p,k,sm2,Anon_24,sl2,
                                   m: res::node<m,p>@M[Orig][] * 
                                   p::sll2<k,sm2,sl2,Anon_24>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                   (
                                   ([sm2<=sl2 & FGE(S,m) & m<=sl2 & v<=m]
                                    [res!=null][true]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; sl; 
                  S](ex)x::sll2<n,sm,sl,S>@M[Orig][LHSCase]@ rem br[{332,331}]&
                  (([sm<=sl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 79::
                              
                              true&(([res=null][0<=n][sm<=sl]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(p_2422,k_2423,sm2_2424,Anon_2425,
                                 sl2_2426,
                                 m_2427: res::node<m_2427,p_2422>@M[Orig][] * 
                                 p_2422::sll2<k_2423,sm2_2424,sl2_2426,Anon_2425>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                 (
                                 ([res!=null]
                                  [{m_2427}<subset> S  & 
                                    sm2_2424<=sl2_2426 & m_2427<=sl2_2426 & 
                                    v<=m_2427]
                                  [0<=n][sm<=sl]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(n:exists(Anon_24:exists(res:exists(q_2295:exists(p:exists(sm2:exists(sl2:exists(v_node_459_715':exists(k:exists(v:exists(sm:exists(qs_2292:exists(ql_2293:exists(sl:exists(v_bool_455_721':exists(x:exists(v_bool_458_720':exists(flted_11_2291:exists(S1_2296:exists(qmin_2294:(-1+
  n=flted_11_2291 & Anon_24=S1_2296 & res=x & q_2295=p & m=qmin_2294 & 
  sm2=qs_2292 & sl2=ql_2293 & v_node_459_715'=x & k=flted_11_2291 & 
  v<=qmin_2294 & sm<=qmin_2294 & qmin_2294<=qs_2292 & qs_2292<=ql_2293 & 
  ql_2293<=sl & flted_11_2291<=-2 & v_bool_455_721'<=0 & x!=null & 
  1<=v_bool_458_720' | -1+n=flted_11_2291 & Anon_24=S1_2296 & res=x & 
  q_2295=p & m=qmin_2294 & sm2=qs_2292 & sl2=ql_2293 & v_node_459_715'=x & 
  k=flted_11_2291 & v<=qmin_2294 & sm<=qmin_2294 & qmin_2294<=qs_2292 & 
  qs_2292<=ql_2293 & ql_2293<=sl & v_bool_455_721'<=0 & x!=null & 
  1<=v_bool_458_720' & 0<=flted_11_2291) & S!=() & S=union(S1_2296,
  {qmin_2294})))))))))))))))))))))) --> FGE(S,m),
 (exists(sm2_2381:exists(qs_2292:exists(ql_2293:exists(sm2:exists(sl:exists(sl_2325:exists(sm_2324:exists(sm:exists(sl2_2383:exists(v:exists(sl2:exists(S1_2296:exists(qmin_2294:sm2_2381=sm2 & 
  qs_2292=sm_2324 & ql_2293=sl_2325 & sm2<=sl2 & (1+qmin_2294)<=v & 
  sl_2325<=sl & sm_2324<=sl_2325 & qmin_2294<=sm_2324 & sm<=qmin_2294 & 
  sl2_2383=sl2 & S_2326=S1_2296 & m_2384=m & v<=m & m<=sl2 & 
  FGE(S_2326,m_2384) & S=union(S1_2296,{qmin_2294}) & 
  S!=())))))))))))))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  GN(S,S2,v)
!!! POST:  S=union(S2,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; xs; xl; 
                    S](ex)x::sll2<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{331}]&
                    (([null!=x][xs<=xl][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(flted_151_119,flted_151_120,lres,sres,
                                S2,v: x'::node<v,flted_151_120>@M[Orig][] * 
                                res::sll2<flted_151_119,sres,lres,S2>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                (
                                ([null=flted_151_120][1+flted_151_119=n]
                                 [sres<=lres & GN(S,S2,v) & v<=sres & 
                                   xs<=v & lres<=xl]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; xl; 
                  S](ex)x::sll2<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{331}]&(
                  ([S!=()]
                   [(n+1)<=0 & xs<=xl & x!=null | xs<=xl & x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              EXISTS(flted_151_2501,flted_151_2502,lres_2503,
                              sres_2504,S2_2505,
                              v_2506: x'::node<v_2506,flted_151_2502>@M[Orig][] * 
                              res::sll2<flted_151_2501,sres_2504,lres_2503,S2_2505>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sres_2504<=lres_2503 & xs<=xl & 
                                 S=union(S2_2505,{v_2506}) & xs<=v_2506 & 
                                 v_2506<=sres_2504 & lres_2503<=xl]
                               [x'!=null][1+flted_151_2501=n & 0<=n]
                               [null=flted_151_2502]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_121':exists(res:exists(q_2463:exists(v_node_155_1120':exists(n:exists(sres:exists(lres:exists(flted_151_120:exists(x:exists(flted_151_119:exists(xs:exists(qs_2460:exists(ql_2461:exists(xl:exists(next_154_1119':exists(x':exists(flted_11_2459:exists(S1_2464:exists(qmin_2462:(tmp_121'=v_node_155_1120' & 
  res=v_node_155_1120' & q_2463=v_node_155_1120' & S1_2464=S2 & -1+
  n=flted_11_2459 & v=qmin_2462 & sres=qs_2460 & lres=ql_2461 & 
  flted_151_120=next_154_1119' & x=x' & flted_151_119=flted_11_2459 & 
  xs<=qmin_2462 & qmin_2462<=qs_2460 & qs_2460<=ql_2461 & ql_2461<=xl & 
  flted_11_2459<=-2 & next_154_1119'=null & x'!=null | 
  tmp_121'=v_node_155_1120' & res=v_node_155_1120' & 
  q_2463=v_node_155_1120' & S1_2464=S2 & -1+n=flted_11_2459 & v=qmin_2462 & 
  sres=qs_2460 & lres=ql_2461 & flted_151_120=next_154_1119' & x=x' & 
  flted_151_119=flted_11_2459 & xs<=qmin_2462 & qmin_2462<=qs_2460 & 
  qs_2460<=ql_2461 & ql_2461<=xl & next_154_1119'=null & x'!=null & 
  0<=flted_11_2459) & S!=() & S=union(S1_2464,
  {qmin_2462}))))))))))))))))))))) --> GN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; sm1; lg1; 
                    S1](ex)x::sll2<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{331}]&
                    (([2<=n][sm1<=lg1][null!=x][S1!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 32::
                                EXISTS(flted_203_110,sm2,lg2,
                                S2: res::sll2<flted_203_110,sm2,lg2,S2>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                (
                                ([2+flted_203_110=n]
                                 [sm2<=lg2 & sm1<=sm2 & lg2<=lg1][GNN(S1,S2)]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; lg1; 
                  S1](ex)x::sll2<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{331}]&
                  (([S1!=()][2<=n][x!=null][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 32::
                              EXISTS(flted_203_2606,sm2_2607,lg2_2608,
                              S2_2609: res::sll2<flted_203_2606,sm2_2607,lg2_2608,S2_2609>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sm2_2607<=lg2_2608 & sm1<=lg1 & 
                                 lg2_2608<=lg1 & sm1<=sm2_2607]
                               [2+flted_203_2606=n & 0<=n]
                               [S2_2609<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(ql_2578:exists(qs_2577:exists(lg1:exists(ql_2535:exists(lg2:exists(sm2:exists(qmin_2579:exists(qs_2534:exists(sm1:exists(S1_2581:exists(S1_2538:exists(qmin_2536:ql_2578=lg2 & 
  qs_2577=sm2 & S1_2538!=() & S1_2538=union(S1_2581,{qmin_2579}) & 
  ql_2535<=lg1 & lg2<=ql_2535 & sm2<=lg2 & qmin_2579<=sm2 & 
  qs_2534<=qmin_2579 & qmin_2536<=qs_2534 & sm1<=qmin_2536 & S1_2581=S2 & 
  S1=union(S1_2538,{qmin_2536}) & S1!=()))))))))))))) --> GNN(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; xs; xl; 
                    S](ex)x::sll2<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{331}]&
                    (([null!=x][xs<=xl][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(flted_185_114,sres,lres,
                                S1: res::sll2<flted_185_114,sres,lres,S1>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                (
                                ([1+flted_185_114=n]
                                 [sres<=lres & lres<=xl & xs<=sres][GT(S,S1)]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; xl; 
                  S](ex)x::sll2<n,xs,xl,S>@M[Orig][LHSCase]@ rem br[{331}]&(
                  ([S!=()]
                   [(n+1)<=0 & xs<=xl & x!=null | xs<=xl & x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(flted_185_2670,sres_2671,lres_2672,
                              S1_2673: res::sll2<flted_185_2670,sres_2671,lres_2672,S1_2673>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sres_2671<=lres_2672 & xs<=xl & 
                                 xs<=sres_2671 & lres_2672<=xl]
                               [1+flted_185_2670=n & 0<=n]
                               [S1_2673<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(q_2641:exists(res:exists(v_node_187_1046':exists(n:exists(sres:exists(lres:exists(flted_185_114:exists(xs:exists(qs_2638:exists(ql_2639:exists(xl:exists(x:exists(flted_11_2637:exists(S1_2642:exists(qmin_2640:(q_2641=v_node_187_1046' & 
  res=v_node_187_1046' & S1=S1_2642 & -1+n=flted_11_2637 & sres=qs_2638 & 
  lres=ql_2639 & flted_185_114=flted_11_2637 & xs<=qmin_2640 & 
  qmin_2640<=qs_2638 & qs_2638<=ql_2639 & ql_2639<=xl & flted_11_2637<=-2 & 
  x!=null | q_2641=v_node_187_1046' & res=v_node_187_1046' & S1=S1_2642 & -1+
  n=flted_11_2637 & sres=qs_2638 & lres=ql_2639 & 
  flted_185_114=flted_11_2637 & xs<=qmin_2640 & qmin_2640<=qs_2638 & 
  qs_2638<=ql_2639 & ql_2639<=xl & x!=null & 0<=flted_11_2637) & 
  S=union(S1_2642,{qmin_2640}) & S!=())))))))))))))))) --> GT(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CPY(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; sm1; lg1; 
                    S1](ex)x::sll1<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{334,333}]&
                    (([true][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 64::
                                EXISTS(n_84,sm1_85,lg1_86,S1_87,n_88,sm1_89,
                                lg1_90,
                                S2: x::sll1<n_84,sm1_85,lg1_86,S1_87>@M[Orig][LHSCase]@ rem br[{334,333}] * 
                                res::sll1<n_88,sm1_89,lg1_90,S2>@M[Orig][LHSCase]@ rem br[{334,333}]&
                                (
                                ([S1=S1_87 & CPY(S1,S2)][n=n_88 & n=n_84]
                                 [sm1_89=sm1 & sm1_89=sm1_85 & lg1=lg1_90 & 
                                   lg1=lg1_86 & sm1_89<=lg1_90]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; lg1; 
                  S1](ex)x::sll1<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{334,333}]&
                  (([sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 64::
                              EXISTS(n_2833,sm1_2834,lg1_2835,S1_2836,n_2837,
                              sm1_2838,lg1_2839,
                              S2_2840: x::sll1<n_2833,sm1_2834,lg1_2835,S1_2836>@M[Orig][LHSCase]@ rem br[{334,333}] * 
                              res::sll1<n_2837,sm1_2838,lg1_2839,S2_2840>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([S1=S1_2836 & S1=S2_2840]
                               [lg1=lg1_2835 & lg1=lg1_2839 & sm1=sm1_2834 & 
                                 sm1=sm1_2838 & sm1<=lg1]
                               [n=n_2833 & n=n_2837 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_87:S2= & S1_87=S1 & S1_87=)) --> CPY(S1,S2),
 (exists(lg1_90:exists(lg1_86:exists(lg1:exists(qs_2706:exists(ql_2707:exists(S1_87:exists(lg1_2715:exists(sm1_2714:exists(sm1:exists(S1_2749:exists(sm1_85:exists(sm1_89:exists(qmin_2747:exists(S1_2778:exists(qmin_2776:exists(S1_2710:exists(qmin_2708:lg1_90=lg1_2715 & 
  lg1_86=lg1_2715 & lg1=lg1_2715 & qs_2706=sm1_2714 & ql_2707=lg1_2715 & 
  S1_87=union(S1_2749,{qmin_2747}) & sm1_2714<=lg1_2715 & 
  qmin_2747<=sm1_2714 & qmin_2708=qmin_2747 & sm1=qmin_2747 & 
  S1_2749=S1_2710 & S1_2716=S1_2710 & S2_2742=S1_2778 & sm1_85=qmin_2747 & 
  sm1_89=qmin_2747 & qmin_2776=qmin_2747 & CPY(S1_2716,S2_2742) & 
  S2=union(S1_2778,{qmin_2776}) & S1!=() & S1=union(S1_2710,
  {qmin_2708}))))))))))))))))))) --> CPY(S1,S2),
 (exists(S1_87:S1_87= & S1=S1_87 & S2=)) --> CPY(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; sm1; lg1; 
                    S1](ex)x::sll1<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{334,333}]&
                    (([true][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::
                                EXISTS(n_92,sm1_93,lg1_94,
                                S2: x::sll1<n_92,sm1_93,lg1_94,S2>@M[Orig][LHSCase]@ rem br[{334,333}]&
                                (
                                ([TRAV(S1,S2)][n=n_92]
                                 [sm1_93=sm1 & lg1=lg1_94 & sm1_93<=lg1_94]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; lg1; 
                  S1](ex)x::sll1<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{334,333}]&
                  (([sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 61::
                              EXISTS(n_3166,sm1_3167,lg1_3168,
                              S2_3169: x::sll1<n_3166,sm1_3167,lg1_3168,S2_3169>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([S1=S2_3169]
                               [lg1=lg1_3168 & sm1=sm1_3167 & sm1<=lg1]
                               [n=n_3166 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(lg1_94:exists(lg1:exists(ql_3091:exists(qs_3090:exists(lg1_3099:exists(sm1_3098:exists(sm1:exists(sm1_93:exists(S1_3122:exists(qmin_3120:exists(S1_3094:exists(qmin_3092:lg1_94=lg1_3099 & 
  lg1=lg1_3099 & ql_3091=lg1_3099 & qs_3090=sm1_3098 & sm1_3098<=lg1_3099 & 
  qmin_3120<=sm1_3098 & qmin_3092=qmin_3120 & sm1=qmin_3120 & 
  S1_3094=S1_3100 & S2_3119=S1_3122 & sm1_93=qmin_3120 & 
  TRAV(S1_3100,S2_3119) & S1!=() & S2=union(S1_3122,{qmin_3120}) & 
  S1=union(S1_3094,{qmin_3092})))))))))))))) --> TRAV(S1,S2),
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
              EBase exists (Expl)(Impl)[m; sm1; lg1; 
                    S1](ex)x::sll2<m,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{331}]&
                    (([null!=x][sm1<=lg1][0!=m][S1!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::ref [x]
                                EXISTS(flted_113_123,sm2,lg2,
                                S2: x'::sll2<flted_113_123,sm2,lg2,S2>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                (
                                ([1+flted_113_123=m]
                                 [sm2<=lg2 & lg2<=lg1 & sm1<=sm2][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; sm1; lg1; 
                  S1](ex)x::sll2<m,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{331}]&
                  (
                  ([S1!=()]
                   [(m+1)<=0 & sm1<=lg1 & x!=null | sm1<=lg1 & x!=null & 1<=m]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 19::ref [x]
                              EXISTS(flted_113_3239,sm2_3240,lg2_3241,
                              S2_3242: x'::sll2<flted_113_3239,sm2_3240,lg2_3241,S2_3242>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sm2_3240<=lg2_3241 & sm1<=lg1 & 
                                 sm1<=sm2_3240 & lg2_3241<=lg1]
                               [1+flted_113_3239=m & 0<=m]
                               [S2_3242<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_124':exists(q_3202:exists(x':exists(sm2:exists(lg2:exists(x:exists(flted_113_123:exists(sm1:exists(qs_3199:exists(ql_3200:exists(lg1:exists(next_117_1141':exists(v_node_118_1142':exists(flted_11_3198:exists(S1_3203:exists(qmin_3201:(-1+
  m=flted_11_3198 & S2=S1_3203 & res=v_node_118_1142' & 
  tmp_124'=v_node_118_1142' & q_3202=x' & sm2=qs_3199 & lg2=ql_3200 & 
  x=v_node_118_1142' & flted_113_123=flted_11_3198 & sm1<=qmin_3201 & 
  qmin_3201<=qs_3199 & qs_3199<=ql_3200 & ql_3200<=lg1 & flted_11_3198<=-2 & 
  next_117_1141'=null & v_node_118_1142'!=null | -1+m=flted_11_3198 & 
  S2=S1_3203 & res=v_node_118_1142' & tmp_124'=v_node_118_1142' & 
  q_3202=x' & sm2=qs_3199 & lg2=ql_3200 & x=v_node_118_1142' & 
  flted_113_123=flted_11_3198 & sm1<=qmin_3201 & qmin_3201<=qs_3199 & 
  qs_3199<=ql_3200 & ql_3200<=lg1 & next_117_1141'=null & 
  v_node_118_1142'!=null & 0<=flted_11_3198) & S1!=() & S1=union(S1_3203,
  {qmin_3201})))))))))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Procedure push_front$node~int SUCCESS

Checking procedure ret_null$node... 
Procedure ret_null$node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; sm; sl; 
                    S](ex)x::sll2<n,sm,sl,S>@M[Orig][LHSCase]@ rem br[{331}]&
                    (([(1+a)<=n & 1<=a][sm<=sl][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::ref [x]
                                EXISTS(sl1,sm2,sl2,n2,n1,sm1,S1,
                                S2: x'::sll2<n1,sm1,sl1,S1>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                                res::sll2<n2,sm2,sl2,S2>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                (
                                ([a=n1 & n=n1+n2][sm=sm1 & sm1<=sl1]
                                 [SPLIT(S,S1,S2)][sm2<=sl2]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; sl; 
                  S](ex)x::sll2<n,sm,sl,S>@M[Orig][LHSCase]@ rem br[{331}]&(
                  ([S!=()][x!=null][sm<=sl][1<=a & (1+a)<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 54::ref [x]
                              EXISTS(sl1_3762,sm2_3763,sl2_3764,n2_3765,
                              n1_3766,sm1_3767,S1_3768,
                              S2_3769: x'::sll2<n1_3766,sm1_3767,sl1_3762,S1_3768>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                              res::sll2<n2_3765,sm2_3763,sl2_3764,S2_3769>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([union(S1_3768,S2_3769)=S][sm2_3763<=sl2_3764]
                               [sm=sm1_3767 & sm1_3767<=sl1_3762 & sm<=sl]
                               [a=n1_3766 & n=n1_3766+n2_3765 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qs_3523:exists(ql_3524:exists(sl1:exists(sl:exists(sl2:exists(sm2:exists(sm1:exists(sm:exists(S1_3638:exists(qmin_3636:exists(S1_3527:exists(qmin_3525:qs_3523=sm2 & 
  ql_3524=sl2 & S1_3527!=() & S1_3638= & 0<=sl1 & qmin_3636<=sl1 & sl2<=sl & 
  sm2<=sl2 & qmin_3636<=sm2 & sm1<=qmin_3636 & sm<=qmin_3636 & 
  qmin_3525=qmin_3636 & S2=S1_3527 & S!=() & S1=union(S1_3638,{qmin_3636}) & 
  S=union(S1_3527,{qmin_3525})))))))))))))) --> SPLIT(S,S1,S2),
 (exists(ql_3573:exists(qs_3572:exists(sl:exists(sl_3579:exists(sl1:exists(sl1_3673:exists(sm_3578:exists(sm1:exists(sm:exists(sm1_3726:exists(S1_3576:exists(qmin_3574:exists(S1_3683:exists(qmin_3681:ql_3573=sl_3579 & 
  qs_3572=sm_3578 & S1_3677!=() & S2_3678!=() & S1_3576!=() & sl_3579<=sl & 
  sm_3578<=sl_3579 & sl1_3673<=sl1 & sm_3578<=sl1_3673 & 
  qmin_3681<=sm_3578 & sm1<=qmin_3681 & sm<=qmin_3681 & 
  sm1_3726<=qmin_3681 & qmin_3574=qmin_3681 & S1_3576=S_3580 & 
  S1_3677=S1_3683 & S2_3678=S2 & SPLIT(S_3580,S1_3677,S2_3678) & 
  S1=union(S1_3683,{qmin_3681}) & S=union(S1_3576,{qmin_3574}) & 
  S1=union(S1_3683,{qmin_3681}) & S!=()))))))))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; sm1; lg1; S1; m; sm2; lg2; 
                    S2](ex)x::sll2<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                    y::sll2<m,sm2,lg2,S2>@M[Orig][LHSCase]@ rem br[{332,331}]&
                    (([true][sm1<=lg1][true][sm2<=lg2]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::ref [x;y]
                                EXISTS(m_129,n_130,smy2,lgy2,S3,smx1,lgx1,
                                S4: x'::sll2<m_129,smy2,lgy2,S3>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                                y'::sll2<n_130,smx1,lgx1,S4>@M[Orig][LHSCase]@ rem br[{332,331}]&
                                (
                                ([m=m_129][n=n_130][smy2<=lgy2][smx1<=lgx1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; lg1; S1; m; sm2; lg2; 
                  S2](ex)x::sll2<n,sm1,lg1,S1>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                  y::sll2<m,sm2,lg2,S2>@M[Orig][LHSCase]@ rem br[{332,331}]&(
                  ([sm1<=lg1][sm2<=lg2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 14::ref [x;y]
                              EXISTS(m_3783,smy2_3784,lgy2_3785,S3_3786,
                              n_3787,smx1_3788,lgx1_3789,
                              S4_3790: x'::sll2<m_3783,smy2_3784,lgy2_3785,S3_3786>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                              y'::sll2<n_3787,smx1_3788,lgx1_3789,S4_3790>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([lg1=lgx1_3789 & sm1=smx1_3788 & sm1<=lg1]
                               [lg2=lgy2_3785 & sm2=smy2_3784 & sm2<=lg2]
                               [m=m_3783 & 0<=m][n=n_3787 & 0<=n][S1=S4_3790]
                               [S2=S3_3786][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (177,13)  (177,4)  (47,17)  (47,24)  (48,7)  (48,14)  (311,4)  (311,11)  (316,4)  (316,11)  (315,10)  (315,4)  (314,9)  (314,13)  (314,4)  (314,4) )

Total verification time: 3.55 second(s)
	Time spent in main process: 0.8 second(s)
	Time spent in child processes: 2.75 second(s)
