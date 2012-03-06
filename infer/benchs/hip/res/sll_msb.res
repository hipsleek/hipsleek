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

Checking procedure assign$node~int~int... Starting Omega...oc

!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    Anon_15](ex)x::sll1<m,Anon_15>@M[Orig][LHSCase]@ rem br[{391,390}]&
                    (([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n1,
                                S: x'::sll1<n1,S>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  Anon_15](ex)x::sll1<m,Anon_15>@M[Orig][LHSCase]@ rem br[{391,390}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              EXISTS(n1_1300,S_1301: true&(
                              ([S_1301=][null=x'][0=n][0=n1_1300][0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(S_1302: x'::sll1<n1,S>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                 (
                                 ([S=S_1302 & 
                                    395::forall(x_1287:x_1287 <notin> S_1302
                                     | x_1287=v) & S_1302!=()]
                                  [x'!=null][n=n1 & 1<=n][0<=m]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure create_list$int~int... 
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
                                                       EAssume 65::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 66::
                                                         EXISTS(n_92,
                                                         S: res::sll1<n_92,S>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                                         (
                                                         ([CL(S,v)][n=n_92]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 67::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(())&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 65::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 66::
                                                       EXISTS(n_1399,
                                                       S_1400: res::sll1<n_1399,S_1400>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                                       (
                                                       ([n=n_1399 & 1<=n]
                                                        [forall(_x:_x <notin> S_1400
                                                           | _x=v)]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 67::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_1355:exists(v_1352:S1_1355= & v_1352=v & S=union(S1_1355,
  {v_1352})))) --> CL(S,v),
 (exists(S1_1372:exists(v_1369:S_1367!=() & S1_1372=S_1367 & v=v_1369 & 
  CL(S_1367,v) & S=union(S1_1372,{v_1369})))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(m,
                                S1: x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([DEL(S,S1)][true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              EXISTS(m_1607,
                              S1_1608: x::sll1<m_1607,S1_1608>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([S1_1608<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1467:exists(S1_1470:exists(S1_1437:exists(v_1434:exists(S1_1549:exists(v_1546:S1_1437!=() & 
  S1_1437=union(S1_1470,{v_1467}) & S1_1549=S1_1470 & v_1434=v_1546 & 
  S=union(S1_1437,{v_1434}) & S1=union(S1_1549,{v_1546}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1502:exists(m_1503:exists(n_1516:exists(a:exists(m_1576:exists(m_1571:exists(v_int_254_1573:exists(n:exists(v_bool_250_844':exists(x:exists(r_1575:exists(m:exists(S1_1577:exists(v_1574:exists(S1_1504:exists(v_1501:S1_1504!=() & 
  S1_1572!=() & (r_1502=r_1575 & S1_1572=S1_1577 & S1_1504=S_1517 & 
  v_1574=v_1501 & 1+m_1503=n & 1+n_1516=n & -1+a=v_int_254_1573 & m=0 & 
  m_1576=-1 & m_1571=-1 & 1<=v_int_254_1573 & (2+v_int_254_1573)<=n & 
  !(v_bool_250_844') & x!=null & r_1575!=null & DEL(S_1517,S1_1572) | 
  r_1502=r_1575 & S1_1572=S1_1577 & S1_1504=S_1517 & v_1574=v_1501 & 1+
  m_1503=n & 1+n_1516=n & -1+a=v_int_254_1573 & 1+m_1576=m & 1+m_1571=m & 
  1<=v_int_254_1573 & (2+v_int_254_1573)<=n & !(v_bool_250_844') & x!=null & 
  r_1575!=null & DEL(S_1517,S1_1572) & 2<=m) & S!=() & S1=union(S1_1577,
  {v_1574}) & S=union(S1_1504,{v_1501})))))))))))))))))) --> DEL(S,S1)]
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 56::
                                EXISTS(m,
                                S1: res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([m<=n & (-1+n)<=m][DEL2(v,S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 56::
                              EXISTS(m_1795,
                              S1_1796: res::sll1<m_1795,S1_1796>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m_1795<=n & 0<=n & (-1+n)<=m_1795]
                               [S1_1796<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1717:exists(v_1714:exists(S1_1635:exists(v_1632:v_1632=v_1714 & 
  S1_1717=S1_1635 & (1+v)<=v_1714 & S1=union(S1_1717,{v_1714}) & S!=() & 
  S=union(S1_1635,{v_1632})))))) --> DEL2(v,S,S1),
 (exists(n:exists(r_1633:exists(res:exists(v_node_272_809':exists(m:exists(v_bool_268_817':exists(x:exists(v_bool_267_819':exists(v_bool_271_816':exists(m_1634:exists(S1_1635:exists(v_1632:(S1_1635=S1 & 
  v_1632=v & -1+n=m_1634 & r_1633=v_node_272_809' & res=v_node_272_809' & 
  m=m_1634 & v_bool_268_817'<=0 & m_1634<=-2 & x!=null & 
  1<=v_bool_267_819' & 1<=v_bool_271_816' | S1_1635=S1 & v_1632=v & -1+
  n=m_1634 & r_1633=v_node_272_809' & res=v_node_272_809' & m=m_1634 & 
  v_bool_268_817'<=0 & x!=null & 1<=v_bool_267_819' & 1<=v_bool_271_816' & 
  0<=m_1634) & S=union(S1_1635,{v_1632}) & 
  S!=()))))))))))))) --> DEL2(v,S,S1),
 (exists(S1_1749:exists(v_1746:exists(S1_1635:exists(v_1632:v_1632=v_1746 & 
  S1_1635=S_1672 & S1_1703=S1_1749 & (1+v_1746)<=v & 
  DEL2(v,S_1672,S1_1703) & S1=union(S1_1749,{v_1746}) & S!=() & 
  S=union(S1_1635,{v_1632})))))) --> DEL2(v,S,S1),
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
!!! POST:  {m}<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 93::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_20,
                                   m: res::node<m,Anon_20>@M[Orig][]&(
                                   ([FGE(S,m) & v<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 93::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1945,
                                 m_1946: res::node<m_1946,Anon_1945>@M[Orig][]&
                                 (
                                 ([res!=null]
                                  [{m_1946}<subset> S  & v<=m_1946][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_20:exists(r_1875:exists(v_node_404_669':exists(m_1876:exists(v:exists(v_bool_400_675':exists(x:exists(v_bool_403_674':exists(n:exists(S1_1877:exists(v_1874:(res=x & 
  Anon_20=r_1875 & m=v_1874 & v_node_404_669'=x & 1+m_1876=n & n<=-1 & 
  v<=v_1874 & v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' | res=x & 
  Anon_20=r_1875 & m=v_1874 & v_node_404_669'=x & 1+m_1876=n & v<=v_1874 & 
  v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' & 1<=n) & S!=() & 
  S=union(S1_1877,{v_1874})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1877:exists(v_1874:(1+v_1874)<=v & S1_1877=S_1902 & 
  m_1928=m & v<=m & FGE(S_1902,m_1928) & S=union(S1_1877,{v_1874}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S2,v)
!!! POST:  S=union(S2,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(flted_141_112,flted_141_113,S2,
                                v: x::node<v,flted_141_113>@M[Orig][] * 
                                res::sll1<flted_141_112,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (
                                ([null=flted_141_113][1+flted_141_112=n]
                                 [GN(S,S2,v)][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(flted_141_2001,flted_141_2002,S2_2003,
                              v_2004: x::node<v_2004,flted_141_2002>@M[Orig][] * 
                              res::sll1<flted_141_2001,S2_2003>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=union(S2_2003,{v_2004})][x!=null]
                               [1+flted_141_2001=n & 0<=n]
                               [null=flted_141_2002]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(tmp_114':exists(res:exists(r_1971:exists(v_node_145_997':exists(flted_141_113:exists(flted_141_112:exists(next_144_996':exists(x:exists(m_1972:exists(S1_1973:exists(v_1970:(-1+
  n=m_1972 & v=v_1970 & S1_1973=S2 & tmp_114'=v_node_145_997' & 
  res=v_node_145_997' & r_1971=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_1972 & next_144_996'=null & 
  m_1972<=-2 & x!=null | -1+n=m_1972 & v=v_1970 & S1_1973=S2 & 
  tmp_114'=v_node_145_997' & res=v_node_145_997' & r_1971=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_1972 & next_144_996'=null & 
  x!=null & 0<=m_1972) & S=union(S1_1973,{v_1970}) & 
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                    ([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::
                                EXISTS(flted_194_102,
                                S2: res::sll1<flted_194_102,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([2+flted_194_102=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::
                              EXISTS(flted_194_2074,
                              S2_2075: res::sll1<flted_194_2074,S2_2075>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([2+flted_194_2074=n & 0<=n]
                               [S2_2075<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2054:exists(S1_2057:exists(S1_2026:exists(v_2023:S1_2026=union(S1_2057,
  {v_2054}) & S1_2026!=() & S2=S1_2057 & S!=() & S=union(S1_2026,
  {v_2023})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(flted_176_106,
                                S1: res::sll1<flted_176_106,S1>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([1+flted_176_106=n][GT(S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              EXISTS(flted_176_2118,
                              S1_2119: res::sll1<flted_176_2118,S1_2119>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_176_2118=n & 0<=n]
                               [S1_2119<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(r_2096:exists(res:exists(v_node_178_943':exists(n:exists(flted_176_106:exists(x:exists(m_2097:exists(S1_2098:exists(v_2095:(r_2096=v_node_178_943' & 
  res=v_node_178_943' & S1_2098=S1 & -1+n=m_2097 & flted_176_106=m_2097 & 
  m_2097<=-2 & x!=null | r_2096=v_node_178_943' & res=v_node_178_943' & 
  S1_2098=S1 & -1+n=m_2097 & flted_176_106=m_2097 & x!=null & 0<=m_2097) & 
  S!=() & S=union(S1_2098,{v_2095}))))))))))) --> GT(S,S1)]
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(flted_204_99,
                                S1: res::sll1<flted_204_99,S1>@M[Orig][LHSCase]@ rem br[{390}]&
                                (
                                ([-1+flted_204_99=n][S1!=() & INS(S,S1,v)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(flted_204_2284,
                              S1_2285: res::sll1<flted_204_2284,S1_2285>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S1_2285  & {v}<subset> S1_2285  & 
                                 S1_2285!=()]
                               [-1+flted_204_2284=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2208:exists(v_2205:S1_2208= & v_2205=v & S= & S1=union(S1_2208,
  {v_2205})))) --> INS(S,S1,v),
 (exists(v_2222:exists(S1_2225:exists(S1_2218:exists(v_2215:exists(S1_2149:exists(v_2146:S1_2218=union(S1_2225,
  {v_2222}) & v_2215<=v_2222 & v_2146=v_2222 & S1_2149=S1_2225 & v=v_2215 & 
  S1=union(S1_2218,{v_2215}) & S=union(S1_2149,{v_2146}) & 
  S!=()))))))) --> INS(S,S1,v),
 (exists(S1_2149:exists(v_2146:exists(S1_2254:exists(v_2251:S1_2199!=() & 
  v_2146=v_2251 & S1_2149=S_2174 & S1_2199=S1_2254 & (1+v_2251)<=v & 
  INS(S_2174,S1_2199,v) & S=union(S1_2149,{v_2146}) & S1=union(S1_2254,
  {v_2251}) & S!=()))))) --> INS(S,S1,v)]
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
                    Anon_18](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                    vn::node<v,Anon_18>@M[Orig][]&(([true][vn!=null]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 46::
                                EXISTS(flted_227_97,
                                S2: res::sll1<flted_227_97,S2>@M[Orig][LHSCase]@ rem br[{390}]&
                                (
                                ([-1+flted_227_97=n][S2!=() & INS2(S,S2,v)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S; v; 
                  Anon_18](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                  vn::node<v,Anon_18>@M[Orig][]&(([vn!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 46::
                              EXISTS(flted_227_2463,
                              S2_2464: res::sll1<flted_227_2463,S2_2464>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S2_2464  & {v}<subset> S2_2464  & 
                                 S2_2464!=()]
                               [-1+flted_227_2463=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2387:exists(v_2384:S1_2387= & v_2384=v & S= & S2=union(S1_2387,
  {v_2384})))) --> INS2(S,S2,v),
 (exists(v_2401:exists(S1_2404:exists(S1_2397:exists(v_2394:exists(S1_2325:exists(v_2322:S1_2397=union(S1_2404,
  {v_2401}) & v_2394<=v_2401 & v_2322=v_2401 & S1_2325=S1_2404 & v=v_2394 & 
  S!=() & S2=union(S1_2397,{v_2394}) & S=union(S1_2325,
  {v_2322})))))))) --> INS2(S,S2,v),
 (exists(S1_2433:exists(v_2430:exists(S1_2325:exists(v_2322:S2_2380!=() & (1+
  v_2430)<=v_2354 & v_2322=v_2430 & S1_2325=S_2353 & S2_2380=S1_2433 & 
  v=v_2354 & INS2(S_2353,S2_2380,v_2354) & S2=union(S1_2433,{v_2430}) & 
  S!=() & S=union(S1_2325,{v_2322})))))) --> INS2(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CPY(S,S1)
!!! POST:  S=S1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 82::
                                EXISTS(n_80,S_81,n_82,
                                S1: x::sll1<n_80,S_81>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                                res::sll1<n_82,S1>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([S=S_81 & CPY(S,S1)][n=n_82 & n=n_80]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 82::
                              EXISTS(n_2592,S_2593,n_2594,
                              S1_2595: x::sll1<n_2592,S_2593>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              res::sll1<n_2594,S1_2595>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=S_2593 & S=S1_2595]
                               [n=n_2592 & n=n_2594 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_81:S1= & S_81=S & S_81=)) --> CPY(S,S1),
 (exists(S_81:exists(S1_2523:exists(v_2520:exists(S1_2536:exists(v_2533:exists(S1_2491:exists(v_2488:S_81=union(S1_2523,
  {v_2520}) & S1_2523=S1_2491 & S_2495=S1_2491 & v_2533=v_2520 & 
  v_2488=v_2520 & S1_2515=S1_2536 & CPY(S_2495,S1_2515) & S1=union(S1_2536,
  {v_2533}) & S=union(S1_2491,{v_2488}) & S!=())))))))) --> CPY(S,S1),
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
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::
                                EXISTS(m,
                                S2: res::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([m<=n][FIL(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 85::
                              EXISTS(m_2754,
                              S2_2755: res::sll1<m_2754,S2_2755>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([m_2754<=n & 0<=n][S2_2755<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2622:exists(v_2619:Anon_11=v & 
  v_2619=v & S1_2622=S_2644 & S2_2706=S2 & FIL(S_2644,S2_2706) & S!=() & 
  S=union(S1_2622,{v_2619})))))) --> FIL(S,S2),
 (exists(r_2714:exists(tmp_79':exists(x:exists(res:exists(m_2715:exists(m_2691:exists(n_2665:exists(n:exists(m:exists(v_bool_377_695':exists(v:exists(v_node_388_697':exists(v_bool_376_696':exists(m_2621:exists(S1_2622:exists(v_2619:exists(S1_2716:exists(v_2713:(r_2714=tmp_79' & 
  x=v_node_388_697' & res=v_node_388_697' & S2_2692=S1_2716 & 
  S1_2622=S_2666 & v_2619=v_2713 & 1+m_2715=m & 1+m_2691=m & n_2665=m_2621 & 
  -1+n=m_2621 & 0<=m & (-1+m)<=m_2621 & !(v_bool_377_695') & (1+v)<=v_2713 & 
  v_node_388_697'!=null & v_bool_376_696' & FIL(S_2666,S2_2692) & 
  0<=m_2621 | r_2714=tmp_79' & x=v_node_388_697' & res=v_node_388_697' & 
  S2_2692=S1_2716 & S1_2622=S_2666 & v_2619=v_2713 & 1+m_2715=m & 1+
  m_2691=m & n_2665=m_2621 & -1+n=m_2621 & 0<=m & (-1+m)<=m_2621 & 
  !(v_bool_377_695') & (1+v_2713)<=v & v_node_388_697'!=null & 
  v_bool_376_696' & FIL(S_2666,S2_2692) & 0<=m_2621) & S=union(S1_2622,
  {v_2619}) & S2=union(S1_2716,{v_2713}) & 
  S!=()))))))))))))))))))) --> FIL(S,S2),
 (S2= & S=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{391,390}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 79::
                                EXISTS(n_84,
                                S2: x::sll1<n_84,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([TRAV(S1,S2)][n=n_84]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 79::
                              EXISTS(n_2839,
                              S2_2840: x::sll1<n_2839,S2_2840>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([S1=S2_2840][n=n_2839 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2806:exists(v_2803:exists(S1_2783:exists(v_2780:v_2803=v_2780 & 
  S1_2783=S1_2787 & S2_2802=S1_2806 & TRAV(S1_2787,S2_2802) & 
  S2=union(S1_2806,{v_2803}) & S1!=() & S1=union(S1_2783,
  {v_2780})))))) --> TRAV(S1,S2),
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
                    S2](ex)x1::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                    x2::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(flted_117_116,
                                S3: res::sll1<flted_117_116,S3>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([flted_117_116=n1+n2][MRG(S3,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x1::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                  x2::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              EXISTS(flted_117_2987,
                              S3_2988: res::sll1<flted_117_2987,S3_2988>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([flted_117_2987=n1+n2 & 0<=n1 & 0<=n2]
                               [S1<subset> S3_2988 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_124_1011':exists(flted_117_116:exists(v_bool_119_1025':exists(x1:exists(x2:exists(v_bool_123_1024':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & n2<=-1 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' | res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2903:exists(S:exists(S1_2877:exists(v_2874:S3_2957!=() & 
  S1_2903!=() & S1_2877!=() & {v_2874}<subset> S1_2903  & S<subset> S1_2903
   & S1_2920=S1_2903 & S1_2877=S2_2922 & S3_2957=S3 & S1=S & 
  MRG(S3_2957,S1_2920,S2_2922) & S2=union(S1_2877,{v_2874}) & S2!=() & 
  S1!=()))))) --> MRG(S3,S1,S2),
 (exists(S:exists(S1_2903:exists(S1_2877:exists(v_2874:S1_2903!=() & 
  S1_2877= & {v_2874}<subset> S1_2903  & S<subset> S1_2903  & S=S1 & 
  S3=S1_2903 & S2=union(S1_2877,{v_2874}) & S2!=() & 
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
                    S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{390}]&(
                    ([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(flted_104_118,
                                S2: x'::sll1<flted_104_118,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([1+flted_104_118=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{390}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(flted_104_3040,
                              S2_3041: x'::sll1<flted_104_3040,S2_3041>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_104_3040=m & 0<=m]
                               [S2_3041<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_119':exists(r_3010:exists(x':exists(x:exists(flted_104_118:exists(next_108_1040':exists(v_node_109_1041':exists(m_3011:exists(S1_3012:exists(v_3009:(-1+
  m=m_3011 & S1_3012=S2 & res=v_node_109_1041' & tmp_119'=v_node_109_1041' & 
  r_3010=x' & x=v_node_109_1041' & flted_104_118=m_3011 & m_3011<=-2 & 
  next_108_1040'=null & v_node_109_1041'!=null | -1+m=m_3011 & S1_3012=S2 & 
  res=v_node_109_1041' & tmp_119'=v_node_109_1041' & r_3010=x' & 
  x=v_node_109_1041' & flted_104_118=m_3011 & next_108_1040'=null & 
  v_node_109_1041'!=null & 0<=m_3011) & S1=union(S1_3012,{v_3009}) & 
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
                    t::sll1<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                    y::sll1<j,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([x!=null][0<=Anon_16][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::ref [x]
                                EXISTS(k,
                                S2: x'::sll1<k,S2>@M[Orig][LHSCase]@ rem br[{390}]&
                                (([-1+k=j][S2!=() & SN(S,S2,v)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig][] * 
                  t::sll1<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                  y::sll1<j,S>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ([x!=null][0<=Anon_16]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::ref [x]
                              EXISTS(k_3096,
                              S2_3097: x'::sll1<k_3096,S2_3097>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=x']
                               [S<subset> S2_3097  & {v}<subset> S2_3097  & 
                                 S2_3097!=()]
                               [-1+k_3096=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S2_3089:exists(S_3071:exists(v_3072:S2_3089!=() & 
  {v_3072}<subset> S2_3089  & S_3071<subset> S2_3089  & S2_3089=S2 & 
  S=S_3071 & v_3072=v)))) --> SN(S,S2,v)]
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

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::ref [x]
                                EXISTS(n1,n2,S1,
                                S2: x'::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{390}] * 
                                res::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{390}]&
                                (
                                ([0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][null!=x']
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{390}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 72::ref [x]
                              EXISTS(n1_3465,n2_3466,S1_3467,
                              S2_3468: x'::sll1<n1_3465,S1_3467>@M[Orig][LHSCase]@ rem br[{390}] * 
                              res::sll1<n2_3466,S2_3468>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([S1_3467!=() & S2_3468!=() & union(S1_3467,
                                 S2_3468)=S]
                               [null!=res][null!=x']
                               [0!=n1_3465 & 0<=n & n=n1_3465+n2_3466 & 
                                 0!=n2_3466]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3279:exists(v_3276:exists(S1_3361:exists(v_3358:S1_3279!=() & 
  S1_3361= & v_3276=v_3358 & S2=S1_3279 & S=union(S1_3279,{v_3276}) & 
  S1=union(S1_3361,{v_3358}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_333_755':exists(tmp_87':exists(xnext_3388:exists(m_3392:exists(m_3317:exists(a:exists(n:exists(n_3319:exists(n1_3384:exists(n2_3385:exists(x':exists(v_bool_322_756':exists(x:exists(res:exists(r_3391:exists(r_3316:exists(a_3389:exists(n1:exists(n2:exists(S1_3393:exists(v_3390:exists(S1_3318:exists(v_3315:S1_3386!=() & 
  S2_3387!=() & S1_3318!=() & (v_node_333_755'=res & tmp_87'=res & 
  xnext_3388=r_3391 & 1+m_3392=n1 & m_3317=-1+n1+n2 & -1+a=a_3389 & n=n1+
  n2 & n_3319=-1+n1+n2 & 1+n1_3384=n1 & n2_3385=n2 & S2_3387=S2 & 
  S1_3386=S1_3393 & S1_3318=S_3320 & v_3390=v_3315 & x'=x & n2<=-1 & 
  !(v_bool_322_756') & x!=null & res!=null & r_3391!=null & r_3316!=null & 
  1<=a_3389 & a_3389<=(-2+n1+n2) & SPLIT(S_3320,S1_3386,S2_3387) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3388=r_3391 & n1=0 & m_3392=-1 & 
  1+m_3317=n2 & -1+a=a_3389 & n=n2 & 1+n_3319=n2 & n1_3384=-1 & n2_3385=n2 & 
  S2_3387=S2 & S1_3386=S1_3393 & S1_3318=S_3320 & v_3390=v_3315 & x'=x & 
  1<=a_3389 & (2+a_3389)<=n2 & !(v_bool_322_756') & x!=null & res!=null & 
  r_3391!=null & r_3316!=null & SPLIT(S_3320,S1_3386,S2_3387) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3388=r_3391 & 1+m_3392=n1 & 
  m_3317=-1+n1+n2 & -1+a=a_3389 & n=n1+n2 & n_3319=-1+n1+n2 & 1+n1_3384=n1 & 
  n2_3385=n2 & S2_3387=S2 & S1_3386=S1_3393 & S1_3318=S_3320 & 
  v_3390=v_3315 & x'=x & !(v_bool_322_756') & x!=null & res!=null & 
  r_3391!=null & r_3316!=null & 2<=n1 & 1<=a_3389 & a_3389<=(-2+n1+n2) & 
  SPLIT(S_3320,S1_3386,S2_3387) & 1<=n2) & S!=() & S1=union(S1_3393,
  {v_3390}) & S=union(S1_3318,
  {v_3315}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                    y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_123,n_124,S3,
                                S4: x'::sll1<m_123,S3>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                                y'::sll1<n_124,S4>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                (([m=m_123][n=n_124]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                  y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{391,390}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(m_3478,S3_3479,n_3480,
                              S4_3481: x'::sll1<m_3478,S3_3479>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              y'::sll1<n_3480,S4_3481>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m=m_3478 & 0<=m][n=n_3480 & 0<=n][S1=S4_3481]
                               [S2=S3_3479][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (168,13)  (168,4)  (39,4)  (39,11)  (40,7)  (40,14)  (304,4)  (304,11)  (309,4)  (309,11)  (308,10)  (308,4)  (307,9)  (307,13)  (307,4)  (307,4) )

Total verification time: 4.2 second(s)
	Time spent in main process: 0.86 second(s)
	Time spent in child processes: 3.34 second(s)
