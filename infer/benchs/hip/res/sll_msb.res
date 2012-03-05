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
                                                       EXISTS(n_1401,
                                                       S_1402: res::sll1<n_1401,S_1402>@M[Orig][LHSCase]@ rem br[{391,390}]&
                                                       (
                                                       ([n=n_1401 & 1<=n]
                                                        [forall(_x:_x <notin> S_1402
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
                              EXISTS(m_1624,
                              S1_1625: x::sll1<m_1624,S1_1625>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([S1_1625<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1469:exists(S1_1472:exists(S1_1439:exists(v_1436:exists(S1_1551:exists(v_1548:S1_1439!=() & 
  S1_1439=union(S1_1472,{v_1469}) & S1_1551=S1_1472 & v_1436=v_1548 & 
  S=union(S1_1439,{v_1436}) & S1=union(S1_1551,{v_1548}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1504:exists(m_1505:exists(n_1518:exists(a:exists(m_1581:exists(m_1576:exists(v_int_254_1578:exists(n:exists(v_bool_250_844':exists(x:exists(r_1580:exists(m:exists(S1_1582:exists(v_1579:exists(S1_1506:exists(v_1503:S1_1506!=() & 
  S1_1577!=() & (r_1504=r_1580 & S1_1577=S1_1582 & S1_1506=S_1519 & 
  v_1579=v_1503 & 1+m_1505=n & 1+n_1518=n & -1+a=v_int_254_1578 & m=0 & 
  m_1581=-1 & m_1576=-1 & 1<=v_int_254_1578 & (2+v_int_254_1578)<=n & 
  !(v_bool_250_844') & x!=null & r_1580!=null & DEL(S_1519,S1_1577) | 
  r_1504=r_1580 & S1_1577=S1_1582 & S1_1506=S_1519 & v_1579=v_1503 & 1+
  m_1505=n & 1+n_1518=n & -1+a=v_int_254_1578 & 1+m_1581=m & 1+m_1576=m & 
  1<=v_int_254_1578 & (2+v_int_254_1578)<=n & !(v_bool_250_844') & x!=null & 
  r_1580!=null & DEL(S_1519,S1_1577) & 2<=m) & S!=() & S1=union(S1_1582,
  {v_1579}) & S=union(S1_1506,{v_1503})))))))))))))))))) --> DEL(S,S1)]
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
                              EXISTS(m_1824,
                              S1_1825: res::sll1<m_1824,S1_1825>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m_1824<=n & 0<=n & (-1+n)<=m_1824]
                               [S1_1825<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1734:exists(v_1731:exists(S1_1652:exists(v_1649:v_1649=v_1731 & 
  S1_1734=S1_1652 & (1+v)<=v_1731 & S1=union(S1_1734,{v_1731}) & S!=() & 
  S=union(S1_1652,{v_1649})))))) --> DEL2(v,S,S1),
 (exists(n:exists(r_1650:exists(res:exists(v_node_272_809':exists(m:exists(v_bool_268_817':exists(x:exists(v_bool_267_819':exists(v_bool_271_816':exists(m_1651:exists(S1_1652:exists(v_1649:(S1_1652=S1 & 
  v_1649=v & -1+n=m_1651 & r_1650=v_node_272_809' & res=v_node_272_809' & 
  m=m_1651 & v_bool_268_817'<=0 & m_1651<=-2 & x!=null & 
  1<=v_bool_267_819' & 1<=v_bool_271_816' | S1_1652=S1 & v_1649=v & -1+
  n=m_1651 & r_1650=v_node_272_809' & res=v_node_272_809' & m=m_1651 & 
  v_bool_268_817'<=0 & x!=null & 1<=v_bool_267_819' & 1<=v_bool_271_816' & 
  0<=m_1651) & S=union(S1_1652,{v_1649}) & 
  S!=()))))))))))))) --> DEL2(v,S,S1),
 (exists(S1_1772:exists(v_1769:exists(S1_1652:exists(v_1649:v_1649=v_1769 & 
  S1_1652=S_1689 & S1_1720=S1_1772 & (1+v_1769)<=v & 
  DEL2(v,S_1689,S1_1720) & S1=union(S1_1772,{v_1769}) & S!=() & 
  S=union(S1_1652,{v_1649})))))) --> DEL2(v,S,S1),
 (S1= & S=) --> DEL2(v,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
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
                              or EXISTS(Anon_1979,
                                 m_1980: res::node<m_1980,Anon_1979>@M[Orig][]&
                                 (
                                 ([res!=null]
                                  [{m_1980}<subset> S  & v<=m_1980][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_20:exists(r_1904:exists(v_node_404_669':exists(m_1905:exists(v:exists(v_bool_400_675':exists(x:exists(v_bool_403_674':exists(n:exists(S1_1906:exists(v_1903:(res=x & 
  Anon_20=r_1904 & m=v_1903 & v_node_404_669'=x & 1+m_1905=n & n<=-1 & 
  v<=v_1903 & v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' | res=x & 
  Anon_20=r_1904 & m=v_1903 & v_node_404_669'=x & 1+m_1905=n & v<=v_1903 & 
  v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' & 1<=n) & S!=() & 
  S=union(S1_1906,{v_1903})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1906:exists(v_1903:(1+v_1903)<=v & S1_1906=S_1931 & 
  m_1960=m & v<=m & FGE(S_1931,m_1960) & S=union(S1_1906,{v_1903}) & 
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
                              EXISTS(flted_141_2038,flted_141_2039,S2_2040,
                              v_2041: x::node<v_2041,flted_141_2039>@M[Orig][] * 
                              res::sll1<flted_141_2038,S2_2040>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=union(S2_2040,{v_2041})][x!=null]
                               [1+flted_141_2038=n & 0<=n]
                               [null=flted_141_2039]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(tmp_114':exists(res:exists(r_2005:exists(v_node_145_997':exists(flted_141_113:exists(flted_141_112:exists(next_144_996':exists(x:exists(m_2006:exists(S1_2007:exists(v_2004:(-1+
  n=m_2006 & v=v_2004 & S1_2007=S2 & tmp_114'=v_node_145_997' & 
  res=v_node_145_997' & r_2005=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_2006 & next_144_996'=null & 
  m_2006<=-2 & x!=null | -1+n=m_2006 & v=v_2004 & S1_2007=S2 & 
  tmp_114'=v_node_145_997' & res=v_node_145_997' & r_2005=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_2006 & next_144_996'=null & 
  x!=null & 0<=m_2006) & S=union(S1_2007,{v_2004}) & 
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
                              EXISTS(flted_194_2113,
                              S2_2114: res::sll1<flted_194_2113,S2_2114>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([2+flted_194_2113=n & 0<=n]
                               [S2_2114<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2091:exists(S1_2094:exists(S1_2063:exists(v_2060:S1_2063=union(S1_2094,
  {v_2091}) & S1_2063!=() & S2=S1_2094 & S!=() & S=union(S1_2063,
  {v_2060})))))) --> GNN(S,S2)]
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
                              EXISTS(flted_176_2160,
                              S1_2161: res::sll1<flted_176_2160,S1_2161>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_176_2160=n & 0<=n]
                               [S1_2161<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(r_2135:exists(res:exists(v_node_178_943':exists(n:exists(flted_176_106:exists(x:exists(m_2136:exists(S1_2137:exists(v_2134:(r_2135=v_node_178_943' & 
  res=v_node_178_943' & S1_2137=S1 & -1+n=m_2136 & flted_176_106=m_2136 & 
  m_2136<=-2 & x!=null | r_2135=v_node_178_943' & res=v_node_178_943' & 
  S1_2137=S1 & -1+n=m_2136 & flted_176_106=m_2136 & x!=null & 0<=m_2136) & 
  S!=() & S=union(S1_2137,{v_2134}))))))))))) --> GT(S,S1)]
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
                              EXISTS(flted_204_2335,
                              S1_2336: res::sll1<flted_204_2335,S1_2336>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S1_2336  & {v}<subset> S1_2336  & 
                                 S1_2336!=()]
                               [-1+flted_204_2335=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2250:exists(v_2247:S1_2250= & v_2247=v & S= & S1=union(S1_2250,
  {v_2247})))) --> INS(S,S1,v),
 (exists(v_2264:exists(S1_2267:exists(S1_2260:exists(v_2257:exists(S1_2191:exists(v_2188:S1_2260=union(S1_2267,
  {v_2264}) & v_2257<=v_2264 & v_2188=v_2264 & S1_2191=S1_2267 & v=v_2257 & 
  S1=union(S1_2260,{v_2257}) & S=union(S1_2191,{v_2188}) & 
  S!=()))))))) --> INS(S,S1,v),
 (exists(S1_2191:exists(v_2188:exists(S1_2299:exists(v_2296:S1_2241!=() & 
  v_2188=v_2296 & S1_2191=S_2216 & S1_2241=S1_2299 & (1+v_2296)<=v & 
  INS(S_2216,S1_2241,v) & S=union(S1_2191,{v_2188}) & S1=union(S1_2299,
  {v_2296}) & S!=()))))) --> INS(S,S1,v)]
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
                              EXISTS(flted_227_2523,
                              S2_2524: res::sll1<flted_227_2523,S2_2524>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S2_2524  & {v}<subset> S2_2524  & 
                                 S2_2524!=()]
                               [-1+flted_227_2523=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2438:exists(v_2435:S1_2438= & v_2435=v & S= & S2=union(S1_2438,
  {v_2435})))) --> INS2(S,S2,v),
 (exists(v_2452:exists(S1_2455:exists(S1_2448:exists(v_2445:exists(S1_2376:exists(v_2373:S1_2448=union(S1_2455,
  {v_2452}) & v_2445<=v_2452 & v_2373=v_2452 & S1_2376=S1_2455 & v=v_2445 & 
  S!=() & S2=union(S1_2448,{v_2445}) & S=union(S1_2376,
  {v_2373})))))))) --> INS2(S,S2,v),
 (exists(S1_2487:exists(v_2484:exists(S1_2376:exists(v_2373:S2_2431!=() & (1+
  v_2484)<=v_2405 & v_2373=v_2484 & S1_2376=S_2404 & S2_2431=S1_2487 & 
  v=v_2405 & INS2(S_2404,S2_2431,v_2405) & S2=union(S1_2487,{v_2484}) & 
  S!=() & S=union(S1_2376,{v_2373})))))) --> INS2(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(S,S1)
!!! POST:  S1=S
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
                              EXISTS(n_2656,S_2657,n_2658,
                              S1_2659: x::sll1<n_2656,S_2657>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              res::sll1<n_2658,S1_2659>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=S_2657 & S=S1_2659]
                               [n=n_2656 & n=n_2658 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_81:S1= & S_81=S & S_81=)) --> CPY(S,S1),
 (exists(S_81:exists(S1_2583:exists(v_2580:exists(S1_2596:exists(v_2593:exists(S1_2551:exists(v_2548:S_81=union(S1_2583,
  {v_2580}) & S1_2583=S1_2551 & S_2555=S1_2551 & v_2593=v_2580 & 
  v_2548=v_2580 & S1_2575=S1_2596 & CPY(S_2555,S1_2575) & S1=union(S1_2596,
  {v_2593}) & S=union(S1_2551,{v_2548}) & S!=())))))))) --> CPY(S,S1),
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
                              EXISTS(m_2827,
                              S2_2828: res::sll1<m_2827,S2_2828>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([m_2827<=n & 0<=n][S2_2828<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2686:exists(v_2683:Anon_11=v & 
  v_2683=v & S1_2686=S_2708 & S2_2770=S2 & FIL(S_2708,S2_2770) & S!=() & 
  S=union(S1_2686,{v_2683})))))) --> FIL(S,S2),
 (exists(r_2779:exists(tmp_79':exists(x:exists(res:exists(m_2780:exists(m_2755:exists(n_2729:exists(n:exists(m:exists(v_bool_377_695':exists(v:exists(v_node_388_697':exists(v_bool_376_696':exists(m_2685:exists(S1_2686:exists(v_2683:exists(S1_2781:exists(v_2778:(r_2779=tmp_79' & 
  x=v_node_388_697' & res=v_node_388_697' & S2_2756=S1_2781 & 
  S1_2686=S_2730 & v_2683=v_2778 & 1+m_2780=m & 1+m_2755=m & n_2729=m_2685 & 
  -1+n=m_2685 & 0<=m & (-1+m)<=m_2685 & !(v_bool_377_695') & (1+v)<=v_2778 & 
  v_node_388_697'!=null & v_bool_376_696' & FIL(S_2730,S2_2756) & 
  0<=m_2685 | r_2779=tmp_79' & x=v_node_388_697' & res=v_node_388_697' & 
  S2_2756=S1_2781 & S1_2686=S_2730 & v_2683=v_2778 & 1+m_2780=m & 1+
  m_2755=m & n_2729=m_2685 & -1+n=m_2685 & 0<=m & (-1+m)<=m_2685 & 
  !(v_bool_377_695') & (1+v_2778)<=v & v_node_388_697'!=null & 
  v_bool_376_696' & FIL(S_2730,S2_2756) & 0<=m_2685) & S=union(S1_2686,
  {v_2683}) & S2=union(S1_2781,{v_2778}) & 
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
                              EXISTS(n_2915,
                              S2_2916: x::sll1<n_2915,S2_2916>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([S1=S2_2916][n=n_2915 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2879:exists(v_2876:exists(S1_2856:exists(v_2853:v_2876=v_2853 & 
  S1_2856=S1_2860 & S2_2875=S1_2879 & TRAV(S1_2860,S2_2875) & 
  S2=union(S1_2879,{v_2876}) & S1!=() & S1=union(S1_2856,
  {v_2853})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_117_3072,
                              S3_3073: res::sll1<flted_117_3072,S3_3073>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([flted_117_3072=n1+n2 & 0<=n1 & 0<=n2]
                               [S1<subset> S3_3073 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_124_1011':exists(flted_117_116:exists(v_bool_119_1025':exists(x1:exists(x2:exists(v_bool_123_1024':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & n2<=-1 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' | res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2979:exists(S:exists(S1_2953:exists(v_2950:S3_3034!=() & 
  S1_2979!=() & S1_2953!=() & {v_2950}<subset> S1_2979  & S<subset> S1_2979
   & S1_2996=S1_2979 & S1_2953=S2_2998 & S3_3034=S3 & S1=S & 
  MRG(S3_3034,S1_2996,S2_2998) & S2=union(S1_2953,{v_2950}) & S2!=() & 
  S1!=()))))) --> MRG(S3,S1,S2),
 (exists(S:exists(S1_2979:exists(S1_2953:exists(v_2950:S1_2979!=() & 
  S1_2953= & {v_2950}<subset> S1_2979  & S<subset> S1_2979  & S=S1 & 
  S3=S1_2979 & S2=union(S1_2953,{v_2950}) & S2!=() & 
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
                              EXISTS(flted_104_3128,
                              S2_3129: x'::sll1<flted_104_3128,S2_3129>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_104_3128=m & 0<=m]
                               [S2_3129<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_119':exists(r_3095:exists(x':exists(x:exists(flted_104_118:exists(next_108_1040':exists(v_node_109_1041':exists(m_3096:exists(S1_3097:exists(v_3094:(-1+
  m=m_3096 & S1_3097=S2 & res=v_node_109_1041' & tmp_119'=v_node_109_1041' & 
  r_3095=x' & x=v_node_109_1041' & flted_104_118=m_3096 & m_3096<=-2 & 
  next_108_1040'=null & v_node_109_1041'!=null | -1+m=m_3096 & S1_3097=S2 & 
  res=v_node_109_1041' & tmp_119'=v_node_109_1041' & r_3095=x' & 
  x=v_node_109_1041' & flted_104_118=m_3096 & next_108_1040'=null & 
  v_node_109_1041'!=null & 0<=m_3096) & S1=union(S1_3097,{v_3094}) & 
  S1!=()))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
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
                              EXISTS(k_3186,
                              S2_3187: x'::sll1<k_3186,S2_3187>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=x']
                               [S<subset> S2_3187  & {v}<subset> S2_3187  & 
                                 S2_3187!=()]
                               [-1+k_3186=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S2_3177:exists(S_3159:exists(v_3160:S2_3177!=() & 
  {v_3160}<subset> S2_3177  & S_3159<subset> S2_3177  & S2_3177=S2 & 
  S=S_3159 & v_3160=v)))) --> SN(S,S2,v)]
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
                              EXISTS(n1_3583,n2_3584,S1_3585,
                              S2_3586: x'::sll1<n1_3583,S1_3585>@M[Orig][LHSCase]@ rem br[{390}] * 
                              res::sll1<n2_3584,S2_3586>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([S1_3585!=() & S2_3586!=() & union(S1_3585,
                                 S2_3586)=S]
                               [null!=res][null!=x']
                               [0!=n1_3583 & 0<=n & n=n1_3583+n2_3584 & 
                                 0!=n2_3584]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3369:exists(v_3366:exists(S1_3451:exists(v_3448:S1_3369!=() & 
  S1_3451= & v_3366=v_3448 & S2=S1_3369 & S=union(S1_3369,{v_3366}) & 
  S1=union(S1_3451,{v_3448}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_333_755':exists(tmp_87':exists(xnext_3479:exists(m_3483:exists(m_3407:exists(a:exists(n:exists(n_3409:exists(n1_3475:exists(n2_3476:exists(x':exists(v_bool_322_756':exists(x:exists(res:exists(r_3482:exists(r_3406:exists(a_3480:exists(n1:exists(n2:exists(S1_3484:exists(v_3481:exists(S1_3408:exists(v_3405:S1_3477!=() & 
  S2_3478!=() & S1_3408!=() & (v_node_333_755'=res & tmp_87'=res & 
  xnext_3479=r_3482 & 1+m_3483=n1 & m_3407=-1+n1+n2 & -1+a=a_3480 & n=n1+
  n2 & n_3409=-1+n1+n2 & 1+n1_3475=n1 & n2_3476=n2 & S2_3478=S2 & 
  S1_3477=S1_3484 & S1_3408=S_3410 & v_3481=v_3405 & x'=x & n2<=-1 & 
  !(v_bool_322_756') & x!=null & res!=null & r_3482!=null & r_3406!=null & 
  1<=a_3480 & a_3480<=(-2+n1+n2) & SPLIT(S_3410,S1_3477,S2_3478) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3479=r_3482 & n1=0 & m_3483=-1 & 
  1+m_3407=n2 & -1+a=a_3480 & n=n2 & 1+n_3409=n2 & n1_3475=-1 & n2_3476=n2 & 
  S2_3478=S2 & S1_3477=S1_3484 & S1_3408=S_3410 & v_3481=v_3405 & x'=x & 
  1<=a_3480 & (2+a_3480)<=n2 & !(v_bool_322_756') & x!=null & res!=null & 
  r_3482!=null & r_3406!=null & SPLIT(S_3410,S1_3477,S2_3478) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3479=r_3482 & 1+m_3483=n1 & 
  m_3407=-1+n1+n2 & -1+a=a_3480 & n=n1+n2 & n_3409=-1+n1+n2 & 1+n1_3475=n1 & 
  n2_3476=n2 & S2_3478=S2 & S1_3477=S1_3484 & S1_3408=S_3410 & 
  v_3481=v_3405 & x'=x & !(v_bool_322_756') & x!=null & res!=null & 
  r_3482!=null & r_3406!=null & 2<=n1 & 1<=a_3480 & a_3480<=(-2+n1+n2) & 
  SPLIT(S_3410,S1_3477,S2_3478) & 1<=n2) & S!=() & S1=union(S1_3484,
  {v_3481}) & S=union(S1_3408,
  {v_3405}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(m_3596,S3_3597,n_3598,
                              S4_3599: x'::sll1<m_3596,S3_3597>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              y'::sll1<n_3598,S4_3599>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m=m_3596 & 0<=m][n=n_3598 & 0<=n][S1=S4_3599]
                               [S2=S3_3597][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (168,13)  (168,4)  (39,4)  (39,11)  (40,7)  (40,14)  (304,4)  (304,11)  (309,4)  (309,11)  (308,10)  (308,4)  (307,9)  (307,13)  (307,4)  (307,4) )

Total verification time: 8.03 second(s)
	Time spent in main process: 0.86 second(s)
	Time spent in child processes: 7.17 second(s)
