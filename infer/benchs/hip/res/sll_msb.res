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
                              EXISTS(m_1792,
                              S1_1793: res::sll1<m_1792,S1_1793>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m_1792<=n & 0<=n & (-1+n)<=m_1792]
                               [S1_1793<subset> S ]))&
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
                              or EXISTS(Anon_1942,
                                 m_1943: res::node<m_1943,Anon_1942>@M[Orig][]&
                                 (
                                 ([res!=null]
                                  [{m_1943}<subset> S  & v<=m_1943][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_20:exists(r_1872:exists(v_node_404_669':exists(m_1873:exists(v:exists(v_bool_400_675':exists(x:exists(v_bool_403_674':exists(n:exists(S1_1874:exists(v_1871:(res=x & 
  Anon_20=r_1872 & m=v_1871 & v_node_404_669'=x & 1+m_1873=n & n<=-1 & 
  v<=v_1871 & v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' | res=x & 
  Anon_20=r_1872 & m=v_1871 & v_node_404_669'=x & 1+m_1873=n & v<=v_1871 & 
  v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' & 1<=n) & S!=() & 
  S=union(S1_1874,{v_1871})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1874:exists(v_1871:(1+v_1871)<=v & S1_1874=S_1899 & 
  m_1925=m & v<=m & FGE(S_1899,m_1925) & S=union(S1_1874,{v_1871}) & 
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
                              EXISTS(flted_141_1998,flted_141_1999,S2_2000,
                              v_2001: x::node<v_2001,flted_141_1999>@M[Orig][] * 
                              res::sll1<flted_141_1998,S2_2000>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=union(S2_2000,{v_2001})][x!=null]
                               [1+flted_141_1998=n & 0<=n]
                               [null=flted_141_1999]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(tmp_114':exists(res:exists(r_1968:exists(v_node_145_997':exists(flted_141_113:exists(flted_141_112:exists(next_144_996':exists(x:exists(m_1969:exists(S1_1970:exists(v_1967:(-1+
  n=m_1969 & v=v_1967 & S1_1970=S2 & tmp_114'=v_node_145_997' & 
  res=v_node_145_997' & r_1968=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_1969 & next_144_996'=null & 
  m_1969<=-2 & x!=null | -1+n=m_1969 & v=v_1967 & S1_1970=S2 & 
  tmp_114'=v_node_145_997' & res=v_node_145_997' & r_1968=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_1969 & next_144_996'=null & 
  x!=null & 0<=m_1969) & S=union(S1_1970,{v_1967}) & 
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
                              EXISTS(flted_194_2071,
                              S2_2072: res::sll1<flted_194_2071,S2_2072>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([2+flted_194_2071=n & 0<=n]
                               [S2_2072<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2051:exists(S1_2054:exists(S1_2023:exists(v_2020:S1_2023=union(S1_2054,
  {v_2051}) & S1_2023!=() & S2=S1_2054 & S!=() & S=union(S1_2023,
  {v_2020})))))) --> GNN(S,S2)]
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
                              EXISTS(flted_176_2115,
                              S1_2116: res::sll1<flted_176_2115,S1_2116>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_176_2115=n & 0<=n]
                               [S1_2116<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(r_2093:exists(res:exists(v_node_178_943':exists(n:exists(flted_176_106:exists(x:exists(m_2094:exists(S1_2095:exists(v_2092:(r_2093=v_node_178_943' & 
  res=v_node_178_943' & S1_2095=S1 & -1+n=m_2094 & flted_176_106=m_2094 & 
  m_2094<=-2 & x!=null | r_2093=v_node_178_943' & res=v_node_178_943' & 
  S1_2095=S1 & -1+n=m_2094 & flted_176_106=m_2094 & x!=null & 0<=m_2094) & 
  S!=() & S=union(S1_2095,{v_2092}))))))))))) --> GT(S,S1)]
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
                              EXISTS(flted_204_2281,
                              S1_2282: res::sll1<flted_204_2281,S1_2282>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S1_2282  & {v}<subset> S1_2282  & 
                                 S1_2282!=()]
                               [-1+flted_204_2281=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2205:exists(v_2202:S1_2205= & v_2202=v & S= & S1=union(S1_2205,
  {v_2202})))) --> INS(S,S1,v),
 (exists(v_2219:exists(S1_2222:exists(S1_2215:exists(v_2212:exists(S1_2146:exists(v_2143:S1_2215=union(S1_2222,
  {v_2219}) & v_2212<=v_2219 & v_2143=v_2219 & S1_2146=S1_2222 & v=v_2212 & 
  S1=union(S1_2215,{v_2212}) & S=union(S1_2146,{v_2143}) & 
  S!=()))))))) --> INS(S,S1,v),
 (exists(S1_2146:exists(v_2143:exists(S1_2251:exists(v_2248:S1_2196!=() & 
  v_2143=v_2248 & S1_2146=S_2171 & S1_2196=S1_2251 & (1+v_2248)<=v & 
  INS(S_2171,S1_2196,v) & S=union(S1_2146,{v_2143}) & S1=union(S1_2251,
  {v_2248}) & S!=()))))) --> INS(S,S1,v)]
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
                              EXISTS(flted_227_2460,
                              S2_2461: res::sll1<flted_227_2460,S2_2461>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S2_2461  & {v}<subset> S2_2461  & 
                                 S2_2461!=()]
                               [-1+flted_227_2460=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2384:exists(v_2381:S1_2384= & v_2381=v & S= & S2=union(S1_2384,
  {v_2381})))) --> INS2(S,S2,v),
 (exists(v_2398:exists(S1_2401:exists(S1_2394:exists(v_2391:exists(S1_2322:exists(v_2319:S1_2394=union(S1_2401,
  {v_2398}) & v_2391<=v_2398 & v_2319=v_2398 & S1_2322=S1_2401 & v=v_2391 & 
  S!=() & S2=union(S1_2394,{v_2391}) & S=union(S1_2322,
  {v_2319})))))))) --> INS2(S,S2,v),
 (exists(S1_2430:exists(v_2427:exists(S1_2322:exists(v_2319:S2_2377!=() & (1+
  v_2427)<=v_2351 & v_2319=v_2427 & S1_2322=S_2350 & S2_2377=S1_2430 & 
  v=v_2351 & INS2(S_2350,S2_2377,v_2351) & S2=union(S1_2430,{v_2427}) & 
  S!=() & S=union(S1_2322,{v_2319})))))) --> INS2(S,S2,v)]
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
                              EXISTS(n_2589,S_2590,n_2591,
                              S1_2592: x::sll1<n_2589,S_2590>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              res::sll1<n_2591,S1_2592>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=S_2590 & S=S1_2592]
                               [n=n_2589 & n=n_2591 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_81:S1= & S_81=S & S_81=)) --> CPY(S,S1),
 (exists(S_81:exists(S1_2520:exists(v_2517:exists(S1_2533:exists(v_2530:exists(S1_2488:exists(v_2485:S_81=union(S1_2520,
  {v_2517}) & S1_2520=S1_2488 & S_2492=S1_2488 & v_2530=v_2517 & 
  v_2485=v_2517 & S1_2512=S1_2533 & CPY(S_2492,S1_2512) & S1=union(S1_2533,
  {v_2530}) & S=union(S1_2488,{v_2485}) & S!=())))))))) --> CPY(S,S1),
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
                              EXISTS(m_2751,
                              S2_2752: res::sll1<m_2751,S2_2752>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([m_2751<=n & 0<=n][S2_2752<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2619:exists(v_2616:Anon_11=v & 
  v_2616=v & S1_2619=S_2641 & S2_2703=S2 & FIL(S_2641,S2_2703) & S!=() & 
  S=union(S1_2619,{v_2616})))))) --> FIL(S,S2),
 (exists(r_2711:exists(tmp_79':exists(x:exists(res:exists(m_2712:exists(m_2688:exists(n_2662:exists(n:exists(m:exists(v_bool_377_695':exists(v:exists(v_node_388_697':exists(v_bool_376_696':exists(m_2618:exists(S1_2619:exists(v_2616:exists(S1_2713:exists(v_2710:(r_2711=tmp_79' & 
  x=v_node_388_697' & res=v_node_388_697' & S2_2689=S1_2713 & 
  S1_2619=S_2663 & v_2616=v_2710 & 1+m_2712=m & 1+m_2688=m & n_2662=m_2618 & 
  -1+n=m_2618 & 0<=m & (-1+m)<=m_2618 & !(v_bool_377_695') & (1+v)<=v_2710 & 
  v_node_388_697'!=null & v_bool_376_696' & FIL(S_2663,S2_2689) & 
  0<=m_2618 | r_2711=tmp_79' & x=v_node_388_697' & res=v_node_388_697' & 
  S2_2689=S1_2713 & S1_2619=S_2663 & v_2616=v_2710 & 1+m_2712=m & 1+
  m_2688=m & n_2662=m_2618 & -1+n=m_2618 & 0<=m & (-1+m)<=m_2618 & 
  !(v_bool_377_695') & (1+v_2710)<=v & v_node_388_697'!=null & 
  v_bool_376_696' & FIL(S_2663,S2_2689) & 0<=m_2618) & S=union(S1_2619,
  {v_2616}) & S2=union(S1_2713,{v_2710}) & 
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
                              EXISTS(n_2836,
                              S2_2837: x::sll1<n_2836,S2_2837>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([S1=S2_2837][n=n_2836 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2803:exists(v_2800:exists(S1_2780:exists(v_2777:v_2800=v_2777 & 
  S1_2780=S1_2784 & S2_2799=S1_2803 & TRAV(S1_2784,S2_2799) & 
  S2=union(S1_2803,{v_2800}) & S1!=() & S1=union(S1_2780,
  {v_2777})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_117_2984,
                              S3_2985: res::sll1<flted_117_2984,S3_2985>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([flted_117_2984=n1+n2 & 0<=n1 & 0<=n2]
                               [S1<subset> S3_2985 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_124_1011':exists(flted_117_116:exists(v_bool_119_1025':exists(x1:exists(x2:exists(v_bool_123_1024':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & n2<=-1 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' | res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2900:exists(S:exists(S1_2874:exists(v_2871:S3_2954!=() & 
  S1_2900!=() & S1_2874!=() & {v_2871}<subset> S1_2900  & S<subset> S1_2900
   & S1_2917=S1_2900 & S1_2874=S2_2919 & S3_2954=S3 & S1=S & 
  MRG(S3_2954,S1_2917,S2_2919) & S2=union(S1_2874,{v_2871}) & S2!=() & 
  S1!=()))))) --> MRG(S3,S1,S2),
 (exists(S:exists(S1_2900:exists(S1_2874:exists(v_2871:S1_2900!=() & 
  S1_2874= & {v_2871}<subset> S1_2900  & S<subset> S1_2900  & S=S1 & 
  S3=S1_2900 & S2=union(S1_2874,{v_2871}) & S2!=() & 
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
                              EXISTS(flted_104_3037,
                              S2_3038: x'::sll1<flted_104_3037,S2_3038>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_104_3037=m & 0<=m]
                               [S2_3038<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_119':exists(r_3007:exists(x':exists(x:exists(flted_104_118:exists(next_108_1040':exists(v_node_109_1041':exists(m_3008:exists(S1_3009:exists(v_3006:(-1+
  m=m_3008 & S1_3009=S2 & res=v_node_109_1041' & tmp_119'=v_node_109_1041' & 
  r_3007=x' & x=v_node_109_1041' & flted_104_118=m_3008 & m_3008<=-2 & 
  next_108_1040'=null & v_node_109_1041'!=null | -1+m=m_3008 & S1_3009=S2 & 
  res=v_node_109_1041' & tmp_119'=v_node_109_1041' & r_3007=x' & 
  x=v_node_109_1041' & flted_104_118=m_3008 & next_108_1040'=null & 
  v_node_109_1041'!=null & 0<=m_3008) & S1=union(S1_3009,{v_3006}) & 
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
                              EXISTS(k_3093,
                              S2_3094: x'::sll1<k_3093,S2_3094>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=x']
                               [S<subset> S2_3094  & {v}<subset> S2_3094  & 
                                 S2_3094!=()]
                               [-1+k_3093=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S2_3086:exists(S_3068:exists(v_3069:S2_3086!=() & 
  {v_3069}<subset> S2_3086  & S_3068<subset> S2_3086  & S2_3086=S2 & 
  S=S_3068 & v_3069=v)))) --> SN(S,S2,v)]
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
                              EXISTS(n1_3462,n2_3463,S1_3464,
                              S2_3465: x'::sll1<n1_3462,S1_3464>@M[Orig][LHSCase]@ rem br[{390}] * 
                              res::sll1<n2_3463,S2_3465>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([S1_3464!=() & S2_3465!=() & union(S1_3464,
                                 S2_3465)=S]
                               [null!=res][null!=x']
                               [0!=n1_3462 & 0<=n & n=n1_3462+n2_3463 & 
                                 0!=n2_3463]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3276:exists(v_3273:exists(S1_3358:exists(v_3355:S1_3276!=() & 
  S1_3358= & v_3273=v_3355 & S2=S1_3276 & S=union(S1_3276,{v_3273}) & 
  S1=union(S1_3358,{v_3355}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_333_755':exists(tmp_87':exists(xnext_3385:exists(m_3389:exists(m_3314:exists(a:exists(n:exists(n_3316:exists(n1_3381:exists(n2_3382:exists(x':exists(v_bool_322_756':exists(x:exists(res:exists(r_3388:exists(r_3313:exists(a_3386:exists(n1:exists(n2:exists(S1_3390:exists(v_3387:exists(S1_3315:exists(v_3312:S1_3383!=() & 
  S2_3384!=() & S1_3315!=() & (v_node_333_755'=res & tmp_87'=res & 
  xnext_3385=r_3388 & 1+m_3389=n1 & m_3314=-1+n1+n2 & -1+a=a_3386 & n=n1+
  n2 & n_3316=-1+n1+n2 & 1+n1_3381=n1 & n2_3382=n2 & S2_3384=S2 & 
  S1_3383=S1_3390 & S1_3315=S_3317 & v_3387=v_3312 & x'=x & n2<=-1 & 
  !(v_bool_322_756') & x!=null & res!=null & r_3388!=null & r_3313!=null & 
  1<=a_3386 & a_3386<=(-2+n1+n2) & SPLIT(S_3317,S1_3383,S2_3384) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3385=r_3388 & n1=0 & m_3389=-1 & 
  1+m_3314=n2 & -1+a=a_3386 & n=n2 & 1+n_3316=n2 & n1_3381=-1 & n2_3382=n2 & 
  S2_3384=S2 & S1_3383=S1_3390 & S1_3315=S_3317 & v_3387=v_3312 & x'=x & 
  1<=a_3386 & (2+a_3386)<=n2 & !(v_bool_322_756') & x!=null & res!=null & 
  r_3388!=null & r_3313!=null & SPLIT(S_3317,S1_3383,S2_3384) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3385=r_3388 & 1+m_3389=n1 & 
  m_3314=-1+n1+n2 & -1+a=a_3386 & n=n1+n2 & n_3316=-1+n1+n2 & 1+n1_3381=n1 & 
  n2_3382=n2 & S2_3384=S2 & S1_3383=S1_3390 & S1_3315=S_3317 & 
  v_3387=v_3312 & x'=x & !(v_bool_322_756') & x!=null & res!=null & 
  r_3388!=null & r_3313!=null & 2<=n1 & 1<=a_3386 & a_3386<=(-2+n1+n2) & 
  SPLIT(S_3317,S1_3383,S2_3384) & 1<=n2) & S!=() & S1=union(S1_3390,
  {v_3387}) & S=union(S1_3315,
  {v_3312}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(m_3475,S3_3476,n_3477,
                              S4_3478: x'::sll1<m_3475,S3_3476>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              y'::sll1<n_3477,S4_3478>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m=m_3475 & 0<=m][n=n_3477 & 0<=n][S1=S4_3478]
                               [S2=S3_3476][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (168,13)  (168,4)  (39,4)  (39,11)  (40,7)  (40,14)  (304,4)  (304,11)  (309,4)  (309,11)  (308,10)  (308,4)  (307,9)  (307,13)  (307,4)  (307,4) )

Total verification time: 3.68 second(s)
	Time spent in main process: 0.75 second(s)
	Time spent in child processes: 2.93 second(s)
