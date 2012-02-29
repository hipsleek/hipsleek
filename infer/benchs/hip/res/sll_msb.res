/usr/local/bin/mona

Processing file "sll_msb.ss"
Parsing sll_msb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure create_list$int~int... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CL(S,v)
!!! POST:  forall(_x:_x <notin> S  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&(([true]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 62::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 63::
                                                         EXISTS(n_92,
                                                         S: res::sll1<n_92,S>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                                         (
                                                         ([CL(S,v)][n=n_92]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 64::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(())&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 62::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 63::
                                                       EXISTS(n_1357,
                                                       S_1358: res::sll1<n_1357,S_1358>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                                       (
                                                       ([n=n_1357 & 1<=n]
                                                        [forall(_x:_x <notin> S_1358
                                                           | _x=v)]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 64::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_1311:exists(v_1308:S1_1311= & v_1308=v & S=union(S1_1311,
  {v_1308})))) --> CL(S,v),
 (exists(S1_1328:exists(v_1325:S_1323!=() & S1_1328=S_1323 & v=v_1325 & 
  CL(S_1323,v) & S=union(S1_1328,{v_1325})))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    Anon_15](ex)x::sll1<m,Anon_15>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n1,
                                S: x'::sll1<n1,S>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  Anon_15](ex)x::sll1<m,Anon_15>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              EXISTS(n1_1380,S_1381: true&(
                              ([S_1381=][null=x'][0=n][0=n1_1380][0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(S_1382: x'::sll1<n1,S>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                 (
                                 ([S=S_1382 & 
                                    432::forall(_x:_x <notin> S_1382  | 
                                    _x=v) & S_1382!=()]
                                  [x'!=null][n=n1 & 1<=n][0<=m]))&
                                 {FLOW,(20,21)=__norm})
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(m,
                                S1: x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([DEL(S,S1)][true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              EXISTS(m_1604,
                              S1_1605: x::sll1<m_1604,S1_1605>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([S1_1605<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1449:exists(S1_1452:exists(S1_1419:exists(v_1416:exists(S1_1531:exists(v_1528:S1_1419!=() & 
  S1_1419=union(S1_1452,{v_1449}) & S1_1531=S1_1452 & v_1416=v_1528 & 
  S=union(S1_1419,{v_1416}) & S1=union(S1_1531,{v_1528}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1484:exists(m_1485:exists(n_1498:exists(a:exists(m_1561:exists(m_1556:exists(v_int_254_1558:exists(n:exists(v_bool_250_828':exists(x:exists(r_1560:exists(m:exists(S1_1562:exists(v_1559:exists(S1_1486:exists(v_1483:S1_1486!=() & 
  S1_1557!=() & (r_1484=r_1560 & S1_1557=S1_1562 & S1_1486=S_1499 & 
  v_1559=v_1483 & 1+m_1485=n & 1+n_1498=n & -1+a=v_int_254_1558 & m=0 & 
  m_1561=-1 & m_1556=-1 & 1<=v_int_254_1558 & (2+v_int_254_1558)<=n & 
  !(v_bool_250_828') & x!=null & r_1560!=null & DEL(S_1499,S1_1557) | 
  r_1484=r_1560 & S1_1557=S1_1562 & S1_1486=S_1499 & v_1559=v_1483 & 1+
  m_1485=n & 1+n_1498=n & -1+a=v_int_254_1558 & 1+m_1561=m & 1+m_1556=m & 
  1<=v_int_254_1558 & (2+v_int_254_1558)<=n & !(v_bool_250_828') & x!=null & 
  r_1560!=null & DEL(S_1499,S1_1557) & 2<=m) & S!=() & S1=union(S1_1562,
  {v_1559}) & S=union(S1_1486,{v_1483})))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL2(v,S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 56::
                                EXISTS(m,
                                S1: res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([m<=n & (-1+n)<=m][DEL2(v,S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 56::
                              EXISTS(m_1802,
                              S1_1803: res::sll1<m_1802,S1_1803>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([m_1802<=n & 0<=n & (-1+n)<=m_1802]
                               [S1_1803<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1714:exists(v_1711:exists(S1_1632:exists(v_1629:v_1629=v_1711 & 
  S1_1714=S1_1632 & (1+v)<=v_1711 & S1=union(S1_1714,{v_1711}) & S!=() & 
  S=union(S1_1632,{v_1629})))))) --> DEL2(v,S,S1),
 (exists(n:exists(r_1630:exists(res:exists(v_node_272_793':exists(m:exists(v_bool_268_801':exists(x:exists(v_bool_267_803':exists(v_bool_271_800':exists(m_1631:exists(S1_1632:exists(v_1629:(S1_1632=S1 & 
  v_1629=v & -1+n=m_1631 & r_1630=v_node_272_793' & res=v_node_272_793' & 
  m=m_1631 & v_bool_268_801'<=0 & m_1631<=-2 & x!=null & 
  1<=v_bool_267_803' & 1<=v_bool_271_800' | S1_1632=S1 & v_1629=v & -1+
  n=m_1631 & r_1630=v_node_272_793' & res=v_node_272_793' & m=m_1631 & 
  v_bool_268_801'<=0 & x!=null & 1<=v_bool_267_803' & 1<=v_bool_271_800' & 
  0<=m_1631) & S=union(S1_1632,{v_1629}) & 
  S!=()))))))))))))) --> DEL2(v,S,S1),
 (exists(S1_1752:exists(v_1749:exists(S1_1632:exists(v_1629:v_1629=v_1749 & 
  S1_1632=S_1669 & S1_1700=S1_1752 & (1+v_1749)<=v & 
  DEL2(v,S_1669,S1_1700) & S1=union(S1_1752,{v_1749}) & S!=() & 
  S=union(S1_1632,{v_1629})))))) --> DEL2(v,S,S1),
 (S1= & S=) --> DEL2(v,S,S1)]
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
!!! POST:  m <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 90::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_20,
                                   m: res::node<m,Anon_20>@M[Orig][]&(
                                   ([FGE(S,m) & v<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 90::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1957,
                                 m_1958: res::node<m_1958,Anon_1957>@M[Orig][]&
                                 (
                                 ([v<=m_1958 & m_1958 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_20:exists(r_1882:exists(v_node_396_668':exists(m_1883:exists(v:exists(v_bool_392_674':exists(x:exists(v_bool_395_673':exists(n:exists(S1_1884:exists(v_1881:(res=x & 
  Anon_20=r_1882 & m=v_1881 & v_node_396_668'=x & 1+m_1883=n & n<=-1 & 
  v<=v_1881 & v_bool_392_674'<=0 & x!=null & 1<=v_bool_395_673' | res=x & 
  Anon_20=r_1882 & m=v_1881 & v_node_396_668'=x & 1+m_1883=n & v<=v_1881 & 
  v_bool_392_674'<=0 & x!=null & 1<=v_bool_395_673' & 1<=n) & S!=() & 
  S=union(S1_1884,{v_1881})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1884:exists(v_1881:(1+v_1881)<=v & S1_1884=S_1909 & 
  m_1938=m & v<=m & FGE(S_1909,m_1938) & S=union(S1_1884,{v_1881}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S2,v)
!!! POST:  S2<subset> S  & v <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(flted_141_111,flted_141_112,S2,
                                v: x::node<v,flted_141_112>@M[Orig][] * 
                                res::sll1<flted_141_111,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (
                                ([null=flted_141_112][1+flted_141_111=n]
                                 [GN(S,S2,v)][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(flted_141_2016,flted_141_2017,S2_2018,
                              v_2019: x::node<v_2019,flted_141_2017>@M[Orig][] * 
                              res::sll1<flted_141_2016,S2_2018>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([S2_2018<subset> S  & v_2019 <in> S ][
                               x!=null][1+flted_141_2016=n & 0<=n]
                               [null=flted_141_2017]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(tmp_113':exists(res:exists(r_1983:exists(v_node_145_981':exists(flted_141_112:exists(flted_141_111:exists(next_144_980':exists(x:exists(m_1984:exists(S1_1985:exists(v_1982:(-1+
  n=m_1984 & v=v_1982 & S1_1985=S2 & tmp_113'=v_node_145_981' & 
  res=v_node_145_981' & r_1983=v_node_145_981' & 
  flted_141_112=next_144_980' & flted_141_111=m_1984 & next_144_980'=null & 
  m_1984<=-2 & x!=null | -1+n=m_1984 & v=v_1982 & S1_1985=S2 & 
  tmp_113'=v_node_145_981' & res=v_node_145_981' & r_1983=v_node_145_981' & 
  flted_141_112=next_144_980' & flted_141_111=m_1984 & next_144_980'=null & 
  x!=null & 0<=m_1984) & S=union(S1_1985,{v_1982}) & 
  S!=()))))))))))))) --> GN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                    ([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::
                                EXISTS(flted_194_101,
                                S2: res::sll1<flted_194_101,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([2+flted_194_101=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::
                              EXISTS(flted_194_2091,
                              S2_2092: res::sll1<flted_194_2091,S2_2092>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([2+flted_194_2091=n & 0<=n]
                               [S2_2092<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2069:exists(S1_2072:exists(S1_2041:exists(v_2038:S1_2041=union(S1_2072,
  {v_2069}) & S1_2041!=() & S2=S1_2072 & S!=() & S=union(S1_2041,
  {v_2038})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(flted_176_105,
                                S1: res::sll1<flted_176_105,S1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([1+flted_176_105=n][GT(S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              EXISTS(flted_176_2138,
                              S1_2139: res::sll1<flted_176_2138,S1_2139>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([1+flted_176_2138=n & 0<=n]
                               [S1_2139<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(r_2113:exists(res:exists(v_node_178_927':exists(n:exists(flted_176_105:exists(x:exists(m_2114:exists(S1_2115:exists(v_2112:(r_2113=v_node_178_927' & 
  res=v_node_178_927' & S1_2115=S1 & -1+n=m_2114 & flted_176_105=m_2114 & 
  m_2114<=-2 & x!=null | r_2113=v_node_178_927' & res=v_node_178_927' & 
  S1_2115=S1 & -1+n=m_2114 & flted_176_105=m_2114 & x!=null & 0<=m_2114) & 
  S!=() & S=union(S1_2115,{v_2112}))))))))))) --> GT(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INS(S,S1,v)
!!! POST:  S<subset> S1  & {v}<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(flted_204_98,
                                S1: res::sll1<flted_204_98,S1>@M[Orig][LHSCase]@ rem br[{387}]&
                                (
                                ([-1+flted_204_98=n][S1!=() & INS(S,S1,v)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(flted_204_2312,
                              S1_2313: res::sll1<flted_204_2312,S1_2313>@M[Orig][LHSCase]@ rem br[{387}]&
                              (
                              ([null!=res]
                               [S<subset> S1_2313  & {v}<subset> S1_2313  & 
                                 S1_2313!=()]
                               [-1+flted_204_2312=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2228:exists(v_2225:S1_2228= & v_2225=v & S= & S1=union(S1_2228,
  {v_2225})))) --> INS(S,S1,v),
 (exists(v_2242:exists(S1_2245:exists(S1_2238:exists(v_2235:exists(S1_2169:exists(v_2166:S1_2238=union(S1_2245,
  {v_2242}) & v_2235<=v_2242 & v_2166=v_2242 & S1_2169=S1_2245 & v=v_2235 & 
  S1=union(S1_2238,{v_2235}) & S=union(S1_2169,{v_2166}) & 
  S!=()))))))) --> INS(S,S1,v),
 (exists(S1_2169:exists(v_2166:exists(S1_2277:exists(v_2274:S1_2219!=() & 
  v_2166=v_2274 & S1_2169=S_2194 & S1_2219=S1_2277 & (1+v_2274)<=v & 
  INS(S_2194,S1_2219,v) & S=union(S1_2169,{v_2166}) & S1=union(S1_2277,
  {v_2274}) & S!=()))))) --> INS(S,S1,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INS2(S,S2,v)
!!! POST:  S<subset> S2  & {v}<subset> S2 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS2]
              EBase exists (Expl)(Impl)[n; S; v; 
                    Anon_18](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    vn::node<v,Anon_18>@M[Orig][]&(([true][vn!=null]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 46::
                                EXISTS(flted_227_96,
                                S2: res::sll1<flted_227_96,S2>@M[Orig][LHSCase]@ rem br[{387}]&
                                (
                                ([-1+flted_227_96=n][S2!=() & INS2(S,S2,v)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S; v; 
                  Anon_18](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  vn::node<v,Anon_18>@M[Orig][]&(([vn!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 46::
                              EXISTS(flted_227_2499,
                              S2_2500: res::sll1<flted_227_2499,S2_2500>@M[Orig][LHSCase]@ rem br[{387}]&
                              (
                              ([null!=res]
                               [S<subset> S2_2500  & {v}<subset> S2_2500  & 
                                 S2_2500!=()]
                               [-1+flted_227_2499=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2415:exists(v_2412:S1_2415= & v_2412=v & S= & S2=union(S1_2415,
  {v_2412})))) --> INS2(S,S2,v),
 (exists(v_2429:exists(S1_2432:exists(S1_2425:exists(v_2422:exists(S1_2353:exists(v_2350:S1_2425=union(S1_2432,
  {v_2429}) & v_2422<=v_2429 & v_2350=v_2429 & S1_2353=S1_2432 & v=v_2422 & 
  S!=() & S2=union(S1_2425,{v_2422}) & S=union(S1_2353,
  {v_2350})))))))) --> INS2(S,S2,v),
 (exists(S1_2464:exists(v_2461:exists(S1_2353:exists(v_2350:S2_2408!=() & (1+
  v_2461)<=v_2382 & v_2350=v_2461 & S1_2353=S_2381 & S2_2408=S1_2464 & 
  v=v_2382 & INS2(S_2381,S2_2408,v_2382) & S2=union(S1_2464,{v_2461}) & 
  S!=() & S=union(S1_2353,{v_2350})))))) --> INS2(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(S,S1)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 79::
                                EXISTS(n_80,S_81,n_82,
                                S1: x::sll1<n_80,S_81>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                                res::sll1<n_82,S1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([S=S_81 & CPY(S,S1)][n=n_82 & n=n_80]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 79::
                              EXISTS(n_2632,S_2633,n_2634,
                              S1_2635: x::sll1<n_2632,S_2633>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                              res::sll1<n_2634,S1_2635>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([S=S_2633 & S=S1_2635]
                               [n=n_2632 & n=n_2634 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_81:S1= & S_81=S & S_81=)) --> CPY(S,S1),
 (exists(S_81:exists(S1_2559:exists(v_2556:exists(S1_2572:exists(v_2569:exists(S1_2527:exists(v_2524:S_81=union(S1_2559,
  {v_2556}) & S1_2559=S1_2527 & S_2531=S1_2527 & v_2569=v_2556 & 
  v_2524=v_2556 & S1_2551=S1_2572 & CPY(S_2531,S1_2551) & S1=union(S1_2572,
  {v_2569}) & S=union(S1_2527,{v_2524}) & S!=())))))))) --> CPY(S,S1),
 (exists(S_81:S_81= & S=S_81 & S1=)) --> CPY(S,S1)]
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 82::
                                EXISTS(m,
                                S2: res::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([m<=n][FIL(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 82::
                              EXISTS(m_2803,
                              S2_2804: res::sll1<m_2803,S2_2804>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([m_2803<=n & 0<=n][S2_2804<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2662:exists(v_2659:Anon_11=v & 
  v_2659=v & S1_2662=S_2684 & S2_2746=S2 & FIL(S_2684,S2_2746) & S!=() & 
  S=union(S1_2662,{v_2659})))))) --> FIL(S,S2),
 (exists(r_2755:exists(tmp_79':exists(x:exists(res:exists(m_2756:exists(m_2731:exists(n_2705:exists(n:exists(m:exists(v_bool_369_694':exists(v:exists(v_node_380_696':exists(v_bool_368_695':exists(m_2661:exists(S1_2662:exists(v_2659:exists(S1_2757:exists(v_2754:(r_2755=tmp_79' & 
  x=v_node_380_696' & res=v_node_380_696' & S2_2732=S1_2757 & 
  S1_2662=S_2706 & v_2659=v_2754 & 1+m_2756=m & 1+m_2731=m & n_2705=m_2661 & 
  -1+n=m_2661 & 0<=m & (-1+m)<=m_2661 & !(v_bool_369_694') & (1+v)<=v_2754 & 
  v_node_380_696'!=null & v_bool_368_695' & FIL(S_2706,S2_2732) & 
  0<=m_2661 | r_2755=tmp_79' & x=v_node_380_696' & res=v_node_380_696' & 
  S2_2732=S1_2757 & S1_2662=S_2706 & v_2659=v_2754 & 1+m_2756=m & 1+
  m_2731=m & n_2705=m_2661 & -1+n=m_2661 & 0<=m & (-1+m)<=m_2661 & 
  !(v_bool_369_694') & (1+v_2754)<=v & v_node_380_696'!=null & 
  v_bool_368_695' & FIL(S_2706,S2_2732) & 0<=m_2661) & S=union(S1_2662,
  {v_2659}) & S2=union(S1_2757,{v_2754}) & 
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
                    S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::
                                EXISTS(n_84,
                                S2: x::sll1<n_84,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([TRAV(S1,S2)][n=n_84]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::
                              EXISTS(n_2891,
                              S2_2892: x::sll1<n_2891,S2_2892>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([S1=S2_2892][n=n_2891 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2855:exists(v_2852:exists(S1_2832:exists(v_2829:v_2852=v_2829 & 
  S1_2832=S1_2836 & S2_2851=S1_2855 & TRAV(S1_2836,S2_2851) & 
  S2=union(S1_2855,{v_2852}) & S1!=() & S1=union(S1_2832,
  {v_2829})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  MRG(S3,S1,S2)
!!! POST:  S1<subset> S3 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG]
              EBase exists (Expl)(Impl)[n1; S1; n2; 
                    S2](ex)x1::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    x2::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(flted_117_115,
                                S3: res::sll1<flted_117_115,S3>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([flted_117_115=n1+n2][MRG(S3,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x1::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  x2::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              EXISTS(flted_117_3048,
                              S3_3049: res::sll1<flted_117_3048,S3_3049>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([flted_117_3048=n1+n2 & 0<=n1 & 0<=n2]
                               [S1<subset> S3_3049 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_124_995':exists(flted_117_115:exists(v_bool_119_1009':exists(x1:exists(x2:exists(v_bool_123_1008':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_124_995'=x2 & flted_117_115=n2 & n2<=-1 & 
  v_bool_119_1009'<=0 & x1=null & x2!=null & 1<=v_bool_123_1008' | res=x2 & 
  S2=S3 & n1=0 & v_node_124_995'=x2 & flted_117_115=n2 & 
  v_bool_119_1009'<=0 & x1=null & x2!=null & 1<=v_bool_123_1008' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2955:exists(S:exists(S1_2929:exists(v_2926:S3_3010!=() & 
  S1_2955!=() & S1_2929!=() & {v_2926}<subset> S1_2955  & S<subset> S1_2955
   & S1_2972=S1_2955 & S1_2929=S2_2974 & S3_3010=S3 & S1=S & 
  MRG(S3_3010,S1_2972,S2_2974) & S2=union(S1_2929,{v_2926}) & S2!=() & 
  S1!=()))))) --> MRG(S3,S1,S2),
 (exists(S:exists(S1_2955:exists(S1_2929:exists(v_2926:S1_2955!=() & 
  S1_2929= & {v_2926}<subset> S1_2955  & S<subset> S1_2955  & S=S1 & 
  S3=S1_2955 & S2=union(S1_2929,{v_2926}) & S2!=() & 
  S1!=()))))) --> MRG(S3,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; 
                    S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{387}]&(
                    ([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(flted_104_117,
                                S2: x'::sll1<flted_104_117,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([1+flted_104_117=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{387}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(flted_104_3104,
                              S2_3105: x'::sll1<flted_104_3104,S2_3105>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([1+flted_104_3104=m & 0<=m]
                               [S2_3105<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_118':exists(r_3071:exists(x':exists(x:exists(flted_104_117:exists(next_108_1024':exists(v_node_109_1025':exists(m_3072:exists(S1_3073:exists(v_3070:(-1+
  m=m_3072 & S1_3073=S2 & res=v_node_109_1025' & tmp_118'=v_node_109_1025' & 
  r_3071=x' & x=v_node_109_1025' & flted_104_117=m_3072 & m_3072<=-2 & 
  next_108_1024'=null & v_node_109_1025'!=null | -1+m=m_3072 & S1_3073=S2 & 
  res=v_node_109_1025' & tmp_118'=v_node_109_1025' & r_3071=x' & 
  x=v_node_109_1025' & flted_104_117=m_3072 & next_108_1024'=null & 
  v_node_109_1025'!=null & 0<=m_3072) & S1=union(S1_3073,{v_3070}) & 
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
!!! POST:  S<subset> S2  & {v}<subset> S2 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                    S](ex)x::node<v,t>@M[Orig][] * 
                    t::sll1<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    y::sll1<j,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([x!=null][0<=Anon_16][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::ref [x]
                                EXISTS(k,
                                S2: x'::sll1<k,S2>@M[Orig][LHSCase]@ rem br[{387}]&
                                (([-1+k=j][S2!=() & SN(S,S2,v)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig][] * 
                  t::sll1<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  y::sll1<j,S>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ([x!=null][0<=Anon_16]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::ref [x]
                              EXISTS(k_3162,
                              S2_3163: x'::sll1<k_3162,S2_3163>@M[Orig][LHSCase]@ rem br[{387}]&
                              (
                              ([null!=x']
                               [S<subset> S2_3163  & {v}<subset> S2_3163  & 
                                 S2_3163!=()]
                               [-1+k_3162=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S2_3153:exists(S_3135:exists(v_3136:S2_3153!=() & 
  {v_3136}<subset> S2_3153  & S_3135<subset> S2_3153  & S2_3153=S2 & 
  S=S_3135 & v_3136=v)))) --> SN(S,S2,v)]
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 69::ref [x]
                                EXISTS(n1,n2,S1,
                                S2: x'::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{387}] * 
                                res::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{387}]&
                                (
                                ([0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][null!=x']
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{387}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 69::ref [x]
                              EXISTS(n1_3559,n2_3560,S1_3561,
                              S2_3562: x'::sll1<n1_3559,S1_3561>@M[Orig][LHSCase]@ rem br[{387}] * 
                              res::sll1<n2_3560,S2_3562>@M[Orig][LHSCase]@ rem br[{387}]&
                              (
                              ([S1_3561!=() & S2_3562!=() & union(S1_3561,
                                 S2_3562)=S]
                               [null!=res][null!=x']
                               [0!=n1_3559 & 0<=n & n=n1_3559+n2_3560 & 
                                 0!=n2_3560]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3345:exists(v_3342:exists(S1_3427:exists(v_3424:S1_3345!=() & 
  S1_3427= & v_3342=v_3424 & S2=S1_3345 & S=union(S1_3345,{v_3342}) & 
  S1=union(S1_3427,{v_3424}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_325_754':exists(tmp_87':exists(xnext_3455:exists(m_3459:exists(m_3383:exists(a:exists(n:exists(n_3385:exists(n1_3451:exists(n2_3452:exists(x':exists(v_bool_314_755':exists(x:exists(res:exists(r_3458:exists(r_3382:exists(a_3456:exists(n1:exists(n2:exists(S1_3460:exists(v_3457:exists(S1_3384:exists(v_3381:S1_3453!=() & 
  S2_3454!=() & S1_3384!=() & (v_node_325_754'=res & tmp_87'=res & 
  xnext_3455=r_3458 & 1+m_3459=n1 & m_3383=-1+n1+n2 & -1+a=a_3456 & n=n1+
  n2 & n_3385=-1+n1+n2 & 1+n1_3451=n1 & n2_3452=n2 & S2_3454=S2 & 
  S1_3453=S1_3460 & S1_3384=S_3386 & v_3457=v_3381 & x'=x & n2<=-1 & 
  !(v_bool_314_755') & x!=null & res!=null & r_3458!=null & r_3382!=null & 
  1<=a_3456 & a_3456<=(-2+n1+n2) & SPLIT(S_3386,S1_3453,S2_3454) | 
  v_node_325_754'=res & tmp_87'=res & xnext_3455=r_3458 & n1=0 & m_3459=-1 & 
  1+m_3383=n2 & -1+a=a_3456 & n=n2 & 1+n_3385=n2 & n1_3451=-1 & n2_3452=n2 & 
  S2_3454=S2 & S1_3453=S1_3460 & S1_3384=S_3386 & v_3457=v_3381 & x'=x & 
  1<=a_3456 & (2+a_3456)<=n2 & !(v_bool_314_755') & x!=null & res!=null & 
  r_3458!=null & r_3382!=null & SPLIT(S_3386,S1_3453,S2_3454) | 
  v_node_325_754'=res & tmp_87'=res & xnext_3455=r_3458 & 1+m_3459=n1 & 
  m_3383=-1+n1+n2 & -1+a=a_3456 & n=n1+n2 & n_3385=-1+n1+n2 & 1+n1_3451=n1 & 
  n2_3452=n2 & S2_3454=S2 & S1_3453=S1_3460 & S1_3384=S_3386 & 
  v_3457=v_3381 & x'=x & !(v_bool_314_755') & x!=null & res!=null & 
  r_3458!=null & r_3382!=null & 2<=n1 & 1<=a_3456 & a_3456<=(-2+n1+n2) & 
  SPLIT(S_3386,S1_3453,S2_3454) & 1<=n2) & S!=() & S1=union(S1_3460,
  {v_3457}) & S=union(S1_3384,
  {v_3381}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_122,n_123,S3,
                                S4: x'::sll1<m_122,S3>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                                y'::sll1<n_123,S4>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([m=m_122][n=n_123]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(m_3572,S3_3573,n_3574,
                              S4_3575: x'::sll1<m_3572,S3_3573>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                              y'::sll1<n_3574,S4_3575>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([m=m_3572 & 0<=m][n=n_3574 & 0<=n][S1=S4_3575]
                               [S2=S3_3573][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (168,13)  (168,4)  (39,4)  (39,11)  (40,7)  (40,14)  (296,4)  (296,11)  (301,4)  (301,11)  (300,10)  (300,4)  (299,9)  (299,13)  (299,4)  (299,4) )

Total verification time: 6.8 second(s)
	Time spent in main process: 0.49 second(s)
	Time spent in child processes: 6.31 second(s)
