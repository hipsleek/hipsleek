/usr/local/bin/mona

Processing file "sll_msb.ss"
Parsing sll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure create_list$int~int... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
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
!!! REL :  FGE(S,m)
!!! POST:  m <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 88::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_19,
                                   m: res::node<m,Anon_19>@M[Orig][]&(
                                   ([FGE(S,m) & v<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 88::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1911,
                                 m_1912: res::node<m_1912,Anon_1911>@M[Orig][]&
                                 (
                                 ([v<=m_1912 & m_1912 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_19:exists(r_1836:exists(v_node_387_665':exists(m_1837:exists(v:exists(v_bool_383_671':exists(x:exists(v_bool_386_670':exists(n:exists(S1_1838:exists(v_1835:(res=x & 
  Anon_19=r_1836 & m=v_1835 & v_node_387_665'=x & 1+m_1837=n & n<=-1 & 
  v<=v_1835 & v_bool_383_671'<=0 & x!=null & 1<=v_bool_386_670' | res=x & 
  Anon_19=r_1836 & m=v_1835 & v_node_387_665'=x & 1+m_1837=n & v<=v_1835 & 
  v_bool_383_671'<=0 & x!=null & 1<=v_bool_386_670' & 1<=n) & S!=() & 
  S=union(S1_1838,{v_1835})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1838:exists(v_1835:(1+v_1835)<=v & S1_1838=S_1863 & 
  m_1892=m & v<=m & FGE(S_1863,m_1892) & S=union(S1_1838,{v_1835}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S2,v)
!!! POST:  S2<subset> S  & v <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(flted_132_109,flted_132_110,S2,
                                v: x::node<v,flted_132_110>@M[Orig][] * 
                                res::sll1<flted_132_109,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_132_110][1+flted_132_109=n]
                                 [GN(S,S2,v)][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              EXISTS(flted_132_1970,flted_132_1971,S2_1972,
                              v_1973: x::node<v_1973,flted_132_1971>@M[Orig][] * 
                              res::sll1<flted_132_1970,S2_1972>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([S2_1972<subset> S  & v_1973 <in> S ][
                               x!=null][1+flted_132_1970=n & 0<=n]
                               [null=flted_132_1971]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(tmp_111':exists(res:exists(r_1937:exists(v_node_136_993':exists(flted_132_110:exists(flted_132_109:exists(next_135_992':exists(x:exists(m_1938:exists(S1_1939:exists(v_1936:(-1+
  n=m_1938 & v=v_1936 & S1_1939=S2 & tmp_111'=v_node_136_993' & 
  res=v_node_136_993' & r_1937=v_node_136_993' & 
  flted_132_110=next_135_992' & flted_132_109=m_1938 & next_135_992'=null & 
  m_1938<=-2 & x!=null | -1+n=m_1938 & v=v_1936 & S1_1939=S2 & 
  tmp_111'=v_node_136_993' & res=v_node_136_993' & r_1937=v_node_136_993' & 
  flted_132_110=next_135_992' & flted_132_109=m_1938 & next_135_992'=null & 
  x!=null & 0<=m_1938) & S=union(S1_1939,{v_1936}) & 
  S!=()))))))))))))) --> GN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_185_99,
                                S2: res::sll1<flted_185_99,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([2+flted_185_99=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_185_2045,
                              S2_2046: res::sll1<flted_185_2045,S2_2046>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([2+flted_185_2045=n & 0<=n]
                               [S2_2046<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2023:exists(S1_2026:exists(S1_1995:exists(v_1992:S1_1995=union(S1_2026,
  {v_2023}) & S1_1995!=() & S2=S1_2026 & S!=() & S=union(S1_1995,
  {v_1992})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_167_103,
                                S1: res::sll1<flted_167_103,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([1+flted_167_103=n][GT(S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(flted_167_2092,
                              S1_2093: res::sll1<flted_167_2092,S1_2093>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([1+flted_167_2092=n & 0<=n]
                               [S1_2093<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(r_2067:exists(res:exists(v_node_169_939':exists(n:exists(flted_167_103:exists(x:exists(m_2068:exists(S1_2069:exists(v_2066:(r_2067=v_node_169_939' & 
  res=v_node_169_939' & S1_2069=S1 & -1+n=m_2068 & flted_167_103=m_2068 & 
  m_2068<=-2 & x!=null | r_2067=v_node_169_939' & res=v_node_169_939' & 
  S1_2069=S1 & -1+n=m_2068 & flted_167_103=m_2068 & x!=null & 0<=m_2068) & 
  S!=() & S=union(S1_2069,{v_2066}))))))))))) --> GT(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(S,S1)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 77::
                                EXISTS(n_78,S_79,n_80,
                                S1: x::sll1<n_78,S_79>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                res::sll1<n_80,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([S=S_79 & CPY(S,S1)][n=n_80 & n=n_78]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 77::
                              EXISTS(n_2574,S_2575,n_2576,
                              S1_2577: x::sll1<n_2574,S_2575>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              res::sll1<n_2576,S1_2577>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([S=S_2575 & S=S1_2577]
                               [n=n_2574 & n=n_2576 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_79:S1= & S_79=S & S_79=)) --> CPY(S,S1),
 (exists(S_79:exists(S1_2501:exists(v_2498:exists(S1_2514:exists(v_2511:exists(S1_2469:exists(v_2466:S_79=union(S1_2501,
  {v_2498}) & S1_2501=S1_2469 & S_2473=S1_2469 & v_2511=v_2498 & 
  v_2466=v_2498 & S1_2493=S1_2514 & CPY(S_2473,S1_2493) & S1=union(S1_2514,
  {v_2511}) & S=union(S1_2469,{v_2466}) & S!=())))))))) --> CPY(S,S1),
 (exists(S_79:S_79= & S=S_79 & S1=)) --> CPY(S,S1)]
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 80::
                                EXISTS(m,
                                S2: res::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([m<=n][FIL(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 80::
                              EXISTS(m_2745,
                              S2_2746: res::sll1<m_2745,S2_2746>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([m_2745<=n & 0<=n][S2_2746<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2604:exists(v_2601:Anon_11=v & 
  v_2601=v & S1_2604=S_2626 & S2_2688=S2 & FIL(S_2626,S2_2688) & S!=() & 
  S=union(S1_2604,{v_2601})))))) --> FIL(S,S2),
 (exists(r_2697:exists(tmp_77':exists(x:exists(res:exists(m_2698:exists(m_2673:exists(n_2647:exists(n:exists(m:exists(v_bool_360_691':exists(v:exists(v_node_371_693':exists(v_bool_359_692':exists(m_2603:exists(S1_2604:exists(v_2601:exists(S1_2699:exists(v_2696:(r_2697=tmp_77' & 
  x=v_node_371_693' & res=v_node_371_693' & S2_2674=S1_2699 & 
  S1_2604=S_2648 & v_2601=v_2696 & 1+m_2698=m & 1+m_2673=m & n_2647=m_2603 & 
  -1+n=m_2603 & 0<=m & (-1+m)<=m_2603 & !(v_bool_360_691') & (1+v)<=v_2696 & 
  v_node_371_693'!=null & v_bool_359_692' & FIL(S_2648,S2_2674) & 
  0<=m_2603 | r_2697=tmp_77' & x=v_node_371_693' & res=v_node_371_693' & 
  S2_2674=S1_2699 & S1_2604=S_2648 & v_2601=v_2696 & 1+m_2698=m & 1+
  m_2673=m & n_2647=m_2603 & -1+n=m_2603 & 0<=m & (-1+m)<=m_2603 & 
  !(v_bool_360_691') & (1+v_2696)<=v & v_node_371_693'!=null & 
  v_bool_359_692' & FIL(S_2648,S2_2674) & 0<=m_2603) & S=union(S1_2604,
  {v_2601}) & S2=union(S1_2699,{v_2696}) & 
  S!=()))))))))))))))))))) --> FIL(S,S2),
 (S2= & S=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 74::
                                EXISTS(n_82,
                                S2: x::sll1<n_82,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([TRAV(S1,S2)][n=n_82]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 74::
                              EXISTS(n_2833,
                              S2_2834: x::sll1<n_2833,S2_2834>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([S1=S2_2834][n=n_2833 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2797:exists(v_2794:exists(S1_2774:exists(v_2771:v_2794=v_2771 & 
  S1_2774=S1_2778 & S2_2793=S1_2797 & TRAV(S1_2778,S2_2793) & 
  S2=union(S1_2797,{v_2794}) & S1!=() & S1=union(S1_2774,
  {v_2771})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; 
                    S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_95_115,
                                S2: x'::sll1<flted_95_115,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([1+flted_95_115=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(flted_95_3056,
                              S2_3057: x'::sll1<flted_95_3056,S2_3057>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([1+flted_95_3056=m & 0<=m]
                               [S2_3057<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_116':exists(r_3023:exists(x':exists(x:exists(flted_95_115:exists(next_99_1038':exists(v_node_100_1039':exists(m_3024:exists(S1_3025:exists(v_3022:(-1+
  m=m_3024 & S1_3025=S2 & res=v_node_100_1039' & tmp_116'=v_node_100_1039' & 
  r_3023=x' & x=v_node_100_1039' & flted_95_115=m_3024 & m_3024<=-2 & 
  next_99_1038'=null & v_node_100_1039'!=null | -1+m=m_3024 & S1_3025=S2 & 
  res=v_node_100_1039' & tmp_116'=v_node_100_1039' & r_3023=x' & 
  x=v_node_100_1039' & flted_95_115=m_3024 & next_99_1038'=null & 
  v_node_100_1039'!=null & 0<=m_3024) & S1=union(S1_3025,{v_3022}) & 
  S1!=()))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SN(S,S2,v)
!!! POST:  S2=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_15; Anon_16; j; 
                    S](ex)x::node<v,t>@M[Orig][] * 
                    t::sll1<Anon_15,Anon_16>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    y::sll1<j,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([x!=null][0<=Anon_15][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::ref [x]
                                EXISTS(k,
                                S2: x'::sll1<k,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                                (([-1+k=j][S2!=() & SN(S,S2,v)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_15; Anon_16; j; 
                  S](ex)x::node<v,t>@M[Orig][] * 
                  t::sll1<Anon_15,Anon_16>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  y::sll1<j,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ([x!=null][0<=Anon_15]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              EXISTS(k_3114,
                              S2_3115: x'::sll1<k_3114,S2_3115>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([S2_3115!=() & S2_3115=union(S,{v})][null!=x']
                               [-1+k_3114=j & 0<=j][0<=Anon_15]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S2_3105:exists(S_3087:exists(v_3088:S2_3105=union(S_3087,
  {v_3088}) & S2_3105=S2 & S=S_3087 & v_3088=v)))) --> SN(S,S2,v)]
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

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 67::ref [x]
                                EXISTS(n1,n2,S1,
                                S2: x'::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{383}] * 
                                res::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                                (
                                ([0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][null!=x']
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 67::ref [x]
                              EXISTS(n1_3511,n2_3512,S1_3513,
                              S2_3514: x'::sll1<n1_3511,S1_3513>@M[Orig][LHSCase]@ rem br[{383}] * 
                              res::sll1<n2_3512,S2_3514>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([S1_3513!=() & S2_3514!=() & union(S1_3513,
                                 S2_3514)=S]
                               [null!=res][null!=x']
                               [0!=n1_3511 & 0<=n & n=n1_3511+n2_3512 & 
                                 0!=n2_3512]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3297:exists(v_3294:exists(S1_3379:exists(v_3376:S1_3297!=() & 
  S1_3379= & v_3294=v_3376 & S2=S1_3297 & S=union(S1_3297,{v_3294}) & 
  S1=union(S1_3379,{v_3376}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_316_751':exists(tmp_85':exists(xnext_3407:exists(m_3411:exists(m_3335:exists(a:exists(n:exists(n_3337:exists(n1_3403:exists(n2_3404:exists(x':exists(v_bool_305_752':exists(x:exists(res:exists(r_3410:exists(r_3334:exists(a_3408:exists(n1:exists(n2:exists(S1_3412:exists(v_3409:exists(S1_3336:exists(v_3333:S1_3405!=() & 
  S2_3406!=() & S1_3336!=() & (v_node_316_751'=res & tmp_85'=res & 
  xnext_3407=r_3410 & 1+m_3411=n1 & m_3335=-1+n1+n2 & -1+a=a_3408 & n=n1+
  n2 & n_3337=-1+n1+n2 & 1+n1_3403=n1 & n2_3404=n2 & S2_3406=S2 & 
  S1_3405=S1_3412 & S1_3336=S_3338 & v_3409=v_3333 & x'=x & n2<=-1 & 
  !(v_bool_305_752') & x!=null & res!=null & r_3410!=null & r_3334!=null & 
  1<=a_3408 & a_3408<=(-2+n1+n2) & SPLIT(S_3338,S1_3405,S2_3406) | 
  v_node_316_751'=res & tmp_85'=res & xnext_3407=r_3410 & n1=0 & m_3411=-1 & 
  1+m_3335=n2 & -1+a=a_3408 & n=n2 & 1+n_3337=n2 & n1_3403=-1 & n2_3404=n2 & 
  S2_3406=S2 & S1_3405=S1_3412 & S1_3336=S_3338 & v_3409=v_3333 & x'=x & 
  1<=a_3408 & (2+a_3408)<=n2 & !(v_bool_305_752') & x!=null & res!=null & 
  r_3410!=null & r_3334!=null & SPLIT(S_3338,S1_3405,S2_3406) | 
  v_node_316_751'=res & tmp_85'=res & xnext_3407=r_3410 & 1+m_3411=n1 & 
  m_3335=-1+n1+n2 & -1+a=a_3408 & n=n1+n2 & n_3337=-1+n1+n2 & 1+n1_3403=n1 & 
  n2_3404=n2 & S2_3406=S2 & S1_3405=S1_3412 & S1_3336=S_3338 & 
  v_3409=v_3333 & x'=x & !(v_bool_305_752') & x!=null & res!=null & 
  r_3410!=null & r_3334!=null & 2<=n1 & 1<=a_3408 & a_3408<=(-2+n1+n2) & 
  SPLIT(S_3338,S1_3405,S2_3406) & 1<=n2) & S!=() & S1=union(S1_3412,
  {v_3409}) & S=union(S1_3336,
  {v_3333}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_120,n_121,S3,
                                S4: x'::sll1<m_120,S3>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                y'::sll1<n_121,S4>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([m=m_120][n=n_121]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(m_3524,S3_3525,n_3526,
                              S4_3527: x'::sll1<m_3524,S3_3525>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              y'::sll1<n_3526,S4_3527>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([m=m_3524 & 0<=m][n=n_3526 & 0<=n][S1=S4_3527]
                               [S2=S3_3525][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (159,13)  (159,4)  (39,4)  (39,11)  (40,7)  (40,14)  (287,4)  (287,11)  (292,4)  (292,11)  (291,10)  (291,4)  (290,9)  (290,13)  (290,4)  (290,4) )

Total verification time: 7.15 second(s)
	Time spent in main process: 1.96 second(s)
	Time spent in child processes: 5.19 second(s)
