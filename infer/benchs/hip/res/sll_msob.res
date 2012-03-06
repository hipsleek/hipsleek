/usr/local/bin/mona

Processing file "sll_msob.ss"
Parsing sll_msob.ss ...
Parsing ../../../prelude.ss ...
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
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              EXISTS(nres_1907,sres_1908,lres_1909,
                              S1_1910: x::sll1<nres_1907,sres_1908,lres_1909,S1_1910>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([sres_1908<=lres_1909 & xs<=xl & 
                                 xs<=sres_1908 & lres_1909<=xl]
                               [1+nres_1907=n & 0<=n][S1_1910<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(xs:exists(xl:exists(ql_1654:exists(ql_1699:exists(qmin_1700:exists(lres:exists(qs_1698:exists(qs_1653:exists(sres:exists(S1_1702:exists(S1_1801:exists(qmin_1799:exists(S1_1657:exists(qmin_1655:xs=sres & 
  xl=lres & ql_1654=lres & ql_1699=lres & qmin_1700=qs_1653 & 
  S1_1657=union(S1_1702,{qmin_1700}) & S1_1657!=() & qs_1698<=lres & 
  qs_1653<=qs_1698 & sres<=qs_1653 & qmin_1655=sres & qmin_1799=sres & 
  S1_1702=S1_1801 & S1=union(S1_1801,{qmin_1799}) & S=union(S1_1657,
  {qmin_1655}) & S!=()))))))))))))))) --> DEL(S1,S),
 (exists(lres_1847:exists(xl_1760:exists(xl:exists(qs_1742:exists(ql_1743:exists(lres:exists(sres_1846:exists(xs_1759:exists(xs:exists(sres:exists(S1_1852:exists(qmin_1850:exists(S1_1746:exists(qmin_1744:lres_1847=lres & 
  xl_1760=ql_1743 & xl=ql_1743 & qs_1742=xs_1759 & S1_1848!=() & 
  S1_1746!=() & lres<=ql_1743 & sres_1846<=lres & xs_1759<=sres_1846 & 
  sres<=xs_1759 & qmin_1744=sres & xs=sres & qmin_1850=sres & 
  S1_1746=S_1761 & S1_1848=S1_1852 & DEL(S1_1848,S_1761) & S!=() & 
  S1=union(S1_1852,{qmin_1850}) & S=union(S1_1746,
  {qmin_1744})))))))))))))))) --> DEL(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
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
                              EXISTS(nres_2189,sres_2190,lres_2191,
                              S1_2192: res::sll1<nres_2189,sres_2190,lres_2191,S1_2192>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([sres_2190<=lres_2191 & xs<=xl & 
                                 xs<=sres_2190 & lres_2191<=xl]
                               [nres_2189<=n & 0<=n & (-1+n)<=nres_2189]
                               [S1_2192<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(q_1946:exists(q_2044:exists(res:exists(xs:exists(xl:exists(n:exists(sres:exists(lres:exists(v_node_280_891':exists(flted_15_1942:exists(qs_1943:exists(ql_1944:exists(x:exists(v_bool_278_915':exists(nres:exists(v_bool_279_905':exists(S1_2045:exists(qmin_2043:exists(S1_1947:exists(qmin_1945:(q_1946=q_2044 & 
  res=x & S1_2045=S1_1947 & qmin_1945=qmin_2043 & xs=qmin_2043 & 
  xl=ql_1944 & n=nres & sres=qmin_2043 & lres=ql_1944 & v_node_280_891'=x & 
  1+flted_15_1942=nres & (1+v)<=qmin_2043 & qmin_2043<=qs_1943 & 
  qs_1943<=ql_1944 & nres<=-1 & x!=null & 1<=v_bool_278_915' & 
  1<=v_bool_279_905' | q_1946=q_2044 & res=x & S1_2045=S1_1947 & 
  qmin_1945=qmin_2043 & xs=qmin_2043 & xl=ql_1944 & n=nres & 
  sres=qmin_2043 & lres=ql_1944 & v_node_280_891'=x & 1+flted_15_1942=nres & 
  (1+v)<=qmin_2043 & qmin_2043<=qs_1943 & qs_1943<=ql_1944 & x!=null & 
  1<=v_bool_278_915' & 1<=nres & 1<=v_bool_279_905') & S1=union(S1_2045,
  {qmin_2043}) & S=union(S1_1947,{qmin_1945}) & 
  S!=()))))))))))))))))))))) --> DEL2(S1,S,v),
 (exists(xs:exists(xl:exists(n:exists(q_1946:exists(res:exists(v_node_283_897':exists(sres:exists(lres:exists(nres:exists(qs_1943:exists(ql_1944:exists(v_bool_279_905':exists(x:exists(v_bool_278_915':exists(v_bool_282_904':exists(flted_15_1942:exists(S1_1947:exists(qmin_1945:(S1=S1_1947 & 
  xs=v & xl=ql_1944 & -1+n=flted_15_1942 & q_1946=v_node_283_897' & 
  res=v_node_283_897' & qmin_1945=v & sres=qs_1943 & lres=ql_1944 & 
  nres=flted_15_1942 & v<=qs_1943 & qs_1943<=ql_1944 & v_bool_279_905'<=0 & 
  flted_15_1942<=-2 & x!=null & 1<=v_bool_278_915' & 1<=v_bool_282_904' | 
  S1=S1_1947 & xs=v & xl=ql_1944 & -1+n=flted_15_1942 & 
  q_1946=v_node_283_897' & res=v_node_283_897' & qmin_1945=v & 
  sres=qs_1943 & lres=ql_1944 & nres=flted_15_1942 & v<=qs_1943 & 
  qs_1943<=ql_1944 & v_bool_279_905'<=0 & x!=null & 1<=v_bool_278_915' & 
  1<=v_bool_282_904' & 0<=flted_15_1942) & S=union(S1_1947,{qmin_1945}) & 
  S!=()))))))))))))))))))) --> DEL2(S1,S,v),
 (exists(lres_2031:exists(ql_1944:exists(xs_1987:exists(xl:exists(xl_1988:exists(lres:exists(sres_2030:exists(qs_1943:exists(xs:exists(sres:exists(S1_2101:exists(qmin_2099:exists(S1_1947:exists(qmin_1945:lres_2031=lres & 
  ql_1944=xl_1988 & xs_1987=qs_1943 & xl=xl_1988 & lres<=xl_1988 & 
  sres_2030<=lres & qs_1943<=sres_2030 & sres<=qs_1943 & xs=sres & 
  qmin_1945=sres & qmin_2099=sres & S1_1947=S_1989 & S1_2032=S1_2101 & (1+
  sres)<=v & DEL2(S1_2032,S_1989,v) & S1=union(S1_2101,{qmin_2099}) & 
  S=union(S1_1947,{qmin_1945}) & S!=()))))))))))))))) --> DEL2(S1,S,v),
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
                              EXISTS(flted_151_2527,flted_151_2528,lres_2529,
                              sres_2530,S2_2531,
                              v_2532: x'::node<v_2532,flted_151_2528>@M[Orig][] * 
                              res::sll2<flted_151_2527,sres_2530,lres_2529,S2_2531>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sres_2530<=lres_2529 & xs<=xl & 
                                 S=union(S2_2531,{v_2532}) & xs<=v_2532 & 
                                 v_2532<=sres_2530 & lres_2529<=xl]
                               [x'!=null][1+flted_151_2527=n & 0<=n]
                               [null=flted_151_2528]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_121':exists(res:exists(q_2489:exists(v_node_155_1121':exists(n:exists(sres:exists(lres:exists(flted_151_120:exists(x:exists(flted_151_119:exists(xs:exists(qs_2486:exists(ql_2487:exists(xl:exists(next_154_1120':exists(x':exists(flted_11_2485:exists(S1_2490:exists(qmin_2488:(tmp_121'=v_node_155_1121' & 
  res=v_node_155_1121' & q_2489=v_node_155_1121' & S1_2490=S2 & -1+
  n=flted_11_2485 & v=qmin_2488 & sres=qs_2486 & lres=ql_2487 & 
  flted_151_120=next_154_1120' & x=x' & flted_151_119=flted_11_2485 & 
  xs<=qmin_2488 & qmin_2488<=qs_2486 & qs_2486<=ql_2487 & ql_2487<=xl & 
  flted_11_2485<=-2 & next_154_1120'=null & x'!=null | 
  tmp_121'=v_node_155_1121' & res=v_node_155_1121' & 
  q_2489=v_node_155_1121' & S1_2490=S2 & -1+n=flted_11_2485 & v=qmin_2488 & 
  sres=qs_2486 & lres=ql_2487 & flted_151_120=next_154_1120' & x=x' & 
  flted_151_119=flted_11_2485 & xs<=qmin_2488 & qmin_2488<=qs_2486 & 
  qs_2486<=ql_2487 & ql_2487<=xl & next_154_1120'=null & x'!=null & 
  0<=flted_11_2485) & S!=() & S=union(S1_2490,
  {qmin_2488}))))))))))))))))))))) --> GN(S,S2,v)]
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
                              EXISTS(flted_203_2632,sm2_2633,lg2_2634,
                              S2_2635: res::sll2<flted_203_2632,sm2_2633,lg2_2634,S2_2635>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sm2_2633<=lg2_2634 & sm1<=lg1 & 
                                 lg2_2634<=lg1 & sm1<=sm2_2633]
                               [2+flted_203_2632=n & 0<=n]
                               [S2_2635<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(ql_2604:exists(qs_2603:exists(lg1:exists(ql_2561:exists(lg2:exists(sm2:exists(qmin_2605:exists(qs_2560:exists(sm1:exists(S1_2607:exists(S1_2564:exists(qmin_2562:ql_2604=lg2 & 
  qs_2603=sm2 & S1_2564!=() & S1_2564=union(S1_2607,{qmin_2605}) & 
  ql_2561<=lg1 & lg2<=ql_2561 & sm2<=lg2 & qmin_2605<=sm2 & 
  qs_2560<=qmin_2605 & qmin_2562<=qs_2560 & sm1<=qmin_2562 & S1_2607=S2 & 
  S1=union(S1_2564,{qmin_2562}) & S1!=()))))))))))))) --> GNN(S1,S2)]
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
                              EXISTS(flted_185_2696,sres_2697,lres_2698,
                              S1_2699: res::sll2<flted_185_2696,sres_2697,lres_2698,S1_2699>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sres_2697<=lres_2698 & xs<=xl & 
                                 xs<=sres_2697 & lres_2698<=xl]
                               [1+flted_185_2696=n & 0<=n]
                               [S1_2699<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(q_2667:exists(res:exists(v_node_187_1047':exists(n:exists(sres:exists(lres:exists(flted_185_114:exists(xs:exists(qs_2664:exists(ql_2665:exists(xl:exists(x:exists(flted_11_2663:exists(S1_2668:exists(qmin_2666:(q_2667=v_node_187_1047' & 
  res=v_node_187_1047' & S1=S1_2668 & -1+n=flted_11_2663 & sres=qs_2664 & 
  lres=ql_2665 & flted_185_114=flted_11_2663 & xs<=qmin_2666 & 
  qmin_2666<=qs_2664 & qs_2664<=ql_2665 & ql_2665<=xl & flted_11_2663<=-2 & 
  x!=null | q_2667=v_node_187_1047' & res=v_node_187_1047' & S1=S1_2668 & -1+
  n=flted_11_2663 & sres=qs_2664 & lres=ql_2665 & 
  flted_185_114=flted_11_2663 & xs<=qmin_2666 & qmin_2666<=qs_2664 & 
  qs_2664<=ql_2665 & ql_2665<=xl & x!=null & 0<=flted_11_2663) & 
  S=union(S1_2668,{qmin_2666}) & S!=())))))))))))))))) --> GT(S,S1)]
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
                              EXISTS(n_2859,sm1_2860,lg1_2861,S1_2862,n_2863,
                              sm1_2864,lg1_2865,
                              S2_2866: x::sll1<n_2859,sm1_2860,lg1_2861,S1_2862>@M[Orig][LHSCase]@ rem br[{334,333}] * 
                              res::sll1<n_2863,sm1_2864,lg1_2865,S2_2866>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([S1=S1_2862 & S1=S2_2866]
                               [lg1=lg1_2861 & lg1=lg1_2865 & sm1=sm1_2860 & 
                                 sm1=sm1_2864 & sm1<=lg1]
                               [n=n_2859 & n=n_2863 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_87:S2= & S1_87=S1 & S1_87=)) --> CPY(S1,S2),
 (exists(lg1_90:exists(lg1_86:exists(lg1:exists(qs_2732:exists(ql_2733:exists(S1_87:exists(lg1_2741:exists(sm1_2740:exists(sm1:exists(S1_2775:exists(sm1_85:exists(sm1_89:exists(qmin_2773:exists(S1_2804:exists(qmin_2802:exists(S1_2736:exists(qmin_2734:lg1_90=lg1_2741 & 
  lg1_86=lg1_2741 & lg1=lg1_2741 & qs_2732=sm1_2740 & ql_2733=lg1_2741 & 
  S1_87=union(S1_2775,{qmin_2773}) & sm1_2740<=lg1_2741 & 
  qmin_2773<=sm1_2740 & qmin_2734=qmin_2773 & sm1=qmin_2773 & 
  S1_2775=S1_2736 & S1_2742=S1_2736 & S2_2768=S1_2804 & sm1_85=qmin_2773 & 
  sm1_89=qmin_2773 & qmin_2802=qmin_2773 & CPY(S1_2742,S2_2768) & 
  S2=union(S1_2804,{qmin_2802}) & S1!=() & S1=union(S1_2736,
  {qmin_2734}))))))))))))))))))) --> CPY(S1,S2),
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
                              EXISTS(n_3192,sm1_3193,lg1_3194,
                              S2_3195: x::sll1<n_3192,sm1_3193,lg1_3194,S2_3195>@M[Orig][LHSCase]@ rem br[{334,333}]&
                              (
                              ([S1=S2_3195]
                               [lg1=lg1_3194 & sm1=sm1_3193 & sm1<=lg1]
                               [n=n_3192 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(lg1_94:exists(lg1:exists(ql_3117:exists(qs_3116:exists(lg1_3125:exists(sm1_3124:exists(sm1:exists(sm1_93:exists(S1_3148:exists(qmin_3146:exists(S1_3120:exists(qmin_3118:lg1_94=lg1_3125 & 
  lg1=lg1_3125 & ql_3117=lg1_3125 & qs_3116=sm1_3124 & sm1_3124<=lg1_3125 & 
  qmin_3146<=sm1_3124 & qmin_3118=qmin_3146 & sm1=qmin_3146 & 
  S1_3120=S1_3126 & S2_3145=S1_3148 & sm1_93=qmin_3146 & 
  TRAV(S1_3126,S2_3145) & S1!=() & S2=union(S1_3148,{qmin_3146}) & 
  S1=union(S1_3120,{qmin_3118})))))))))))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_113_3265,sm2_3266,lg2_3267,
                              S2_3268: x'::sll2<flted_113_3265,sm2_3266,lg2_3267,S2_3268>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([sm2_3266<=lg2_3267 & sm1<=lg1 & 
                                 sm1<=sm2_3266 & lg2_3267<=lg1]
                               [1+flted_113_3265=m & 0<=m]
                               [S2_3268<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_124':exists(q_3228:exists(x':exists(sm2:exists(lg2:exists(x:exists(flted_113_123:exists(sm1:exists(qs_3225:exists(ql_3226:exists(lg1:exists(next_117_1142':exists(v_node_118_1143':exists(flted_11_3224:exists(S1_3229:exists(qmin_3227:(-1+
  m=flted_11_3224 & S2=S1_3229 & res=v_node_118_1143' & 
  tmp_124'=v_node_118_1143' & q_3228=x' & sm2=qs_3225 & lg2=ql_3226 & 
  x=v_node_118_1143' & flted_113_123=flted_11_3224 & sm1<=qmin_3227 & 
  qmin_3227<=qs_3225 & qs_3225<=ql_3226 & ql_3226<=lg1 & flted_11_3224<=-2 & 
  next_117_1142'=null & v_node_118_1143'!=null | -1+m=flted_11_3224 & 
  S2=S1_3229 & res=v_node_118_1143' & tmp_124'=v_node_118_1143' & 
  q_3228=x' & sm2=qs_3225 & lg2=ql_3226 & x=v_node_118_1143' & 
  flted_113_123=flted_11_3224 & sm1<=qmin_3227 & qmin_3227<=qs_3225 & 
  qs_3225<=ql_3226 & ql_3226<=lg1 & next_117_1142'=null & 
  v_node_118_1143'!=null & 0<=flted_11_3224) & S1!=() & S1=union(S1_3229,
  {qmin_3227})))))))))))))))))))) --> PF(S1,S2)]
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
                              EXISTS(sl1_3788,sm2_3789,sl2_3790,n2_3791,
                              n1_3792,sm1_3793,S1_3794,
                              S2_3795: x'::sll2<n1_3792,sm1_3793,sl1_3788,S1_3794>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                              res::sll2<n2_3791,sm2_3789,sl2_3790,S2_3795>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([union(S1_3794,S2_3795)=S][sm2_3789<=sl2_3790]
                               [sm=sm1_3793 & sm1_3793<=sl1_3788 & sm<=sl]
                               [a=n1_3792 & n=n1_3792+n2_3791 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qs_3549:exists(ql_3550:exists(sl1:exists(sl:exists(sl2:exists(sm2:exists(sm1:exists(sm:exists(S1_3664:exists(qmin_3662:exists(S1_3553:exists(qmin_3551:qs_3549=sm2 & 
  ql_3550=sl2 & S1_3553!=() & S1_3664= & 0<=sl1 & qmin_3662<=sl1 & sl2<=sl & 
  sm2<=sl2 & qmin_3662<=sm2 & sm1<=qmin_3662 & sm<=qmin_3662 & 
  qmin_3551=qmin_3662 & S2=S1_3553 & S!=() & S1=union(S1_3664,{qmin_3662}) & 
  S=union(S1_3553,{qmin_3551})))))))))))))) --> SPLIT(S,S1,S2),
 (exists(ql_3599:exists(qs_3598:exists(sl:exists(sl_3605:exists(sl1:exists(sl1_3699:exists(sm_3604:exists(sm1:exists(sm:exists(sm1_3752:exists(S1_3602:exists(qmin_3600:exists(S1_3709:exists(qmin_3707:ql_3599=sl_3605 & 
  qs_3598=sm_3604 & S1_3703!=() & S2_3704!=() & S1_3602!=() & sl_3605<=sl & 
  sm_3604<=sl_3605 & sl1_3699<=sl1 & sm_3604<=sl1_3699 & 
  qmin_3707<=sm_3604 & sm1<=qmin_3707 & sm<=qmin_3707 & 
  sm1_3752<=qmin_3707 & qmin_3600=qmin_3707 & S1_3602=S_3606 & 
  S1_3703=S1_3709 & S2_3704=S2 & SPLIT(S_3606,S1_3703,S2_3704) & 
  S1=union(S1_3709,{qmin_3707}) & S=union(S1_3602,{qmin_3600}) & 
  S1=union(S1_3709,{qmin_3707}) & S!=()))))))))))))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(m_3809,smy2_3810,lgy2_3811,S3_3812,
                              n_3813,smx1_3814,lgx1_3815,
                              S4_3816: x'::sll2<m_3809,smy2_3810,lgy2_3811,S3_3812>@M[Orig][LHSCase]@ rem br[{332,331}] * 
                              y'::sll2<n_3813,smx1_3814,lgx1_3815,S4_3816>@M[Orig][LHSCase]@ rem br[{332,331}]&
                              (
                              ([lg1=lgx1_3815 & sm1=smx1_3814 & sm1<=lg1]
                               [lg2=lgy2_3811 & sm2=smy2_3810 & sm2<=lg2]
                               [m=m_3809 & 0<=m][n=n_3813 & 0<=n][S1=S4_3816]
                               [S2=S3_3812][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (177,13)  (177,4)  (47,17)  (47,24)  (48,7)  (48,14)  (311,4)  (311,11)  (316,4)  (316,11)  (315,10)  (315,4)  (314,9)  (314,13)  (314,4)  (314,4) )

Total verification time: 6.12 second(s)
	Time spent in main process: 3.46 second(s)
	Time spent in child processes: 2.66 second(s)
