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
                              EXISTS(m_1822,
                              S1_1823: res::sll1<m_1822,S1_1823>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m_1822<=n & 0<=n & (-1+n)<=m_1822]
                               [S1_1823<subset> S ]))&
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
!!! POST:  m <in> S 
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
                              or EXISTS(Anon_1977,
                                 m_1978: res::node<m_1978,Anon_1977>@M[Orig][]&
                                 (
                                 ([v<=m_1978 & m_1978 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_20:exists(r_1902:exists(v_node_404_669':exists(m_1903:exists(v:exists(v_bool_400_675':exists(x:exists(v_bool_403_674':exists(n:exists(S1_1904:exists(v_1901:(res=x & 
  Anon_20=r_1902 & m=v_1901 & v_node_404_669'=x & 1+m_1903=n & n<=-1 & 
  v<=v_1901 & v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' | res=x & 
  Anon_20=r_1902 & m=v_1901 & v_node_404_669'=x & 1+m_1903=n & v<=v_1901 & 
  v_bool_400_675'<=0 & x!=null & 1<=v_bool_403_674' & 1<=n) & S!=() & 
  S=union(S1_1904,{v_1901})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1904:exists(v_1901:(1+v_1901)<=v & S1_1904=S_1929 & 
  m_1958=m & v<=m & FGE(S_1929,m_1958) & S=union(S1_1904,{v_1901}) & 
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
                              EXISTS(flted_141_2036,flted_141_2037,S2_2038,
                              v_2039: x::node<v_2039,flted_141_2037>@M[Orig][] * 
                              res::sll1<flted_141_2036,S2_2038>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S2_2038<subset> S  & v_2039 <in> S ][
                               x!=null][1+flted_141_2036=n & 0<=n]
                               [null=flted_141_2037]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(tmp_114':exists(res:exists(r_2003:exists(v_node_145_997':exists(flted_141_113:exists(flted_141_112:exists(next_144_996':exists(x:exists(m_2004:exists(S1_2005:exists(v_2002:(-1+
  n=m_2004 & v=v_2002 & S1_2005=S2 & tmp_114'=v_node_145_997' & 
  res=v_node_145_997' & r_2003=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_2004 & next_144_996'=null & 
  m_2004<=-2 & x!=null | -1+n=m_2004 & v=v_2002 & S1_2005=S2 & 
  tmp_114'=v_node_145_997' & res=v_node_145_997' & r_2003=v_node_145_997' & 
  flted_141_113=next_144_996' & flted_141_112=m_2004 & next_144_996'=null & 
  x!=null & 0<=m_2004) & S=union(S1_2005,{v_2002}) & 
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
                              EXISTS(flted_194_2111,
                              S2_2112: res::sll1<flted_194_2111,S2_2112>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([2+flted_194_2111=n & 0<=n]
                               [S2_2112<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2089:exists(S1_2092:exists(S1_2061:exists(v_2058:S1_2061=union(S1_2092,
  {v_2089}) & S1_2061!=() & S2=S1_2092 & S!=() & S=union(S1_2061,
  {v_2058})))))) --> GNN(S,S2)]
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
                              EXISTS(flted_176_2158,
                              S1_2159: res::sll1<flted_176_2158,S1_2159>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_176_2158=n & 0<=n]
                               [S1_2159<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(r_2133:exists(res:exists(v_node_178_943':exists(n:exists(flted_176_106:exists(x:exists(m_2134:exists(S1_2135:exists(v_2132:(r_2133=v_node_178_943' & 
  res=v_node_178_943' & S1_2135=S1 & -1+n=m_2134 & flted_176_106=m_2134 & 
  m_2134<=-2 & x!=null | r_2133=v_node_178_943' & res=v_node_178_943' & 
  S1_2135=S1 & -1+n=m_2134 & flted_176_106=m_2134 & x!=null & 0<=m_2134) & 
  S!=() & S=union(S1_2135,{v_2132}))))))))))) --> GT(S,S1)]
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
                              EXISTS(flted_204_2332,
                              S1_2333: res::sll1<flted_204_2332,S1_2333>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S1_2333  & {v}<subset> S1_2333  & 
                                 S1_2333!=()]
                               [-1+flted_204_2332=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2248:exists(v_2245:S1_2248= & v_2245=v & S= & S1=union(S1_2248,
  {v_2245})))) --> INS(S,S1,v),
 (exists(v_2262:exists(S1_2265:exists(S1_2258:exists(v_2255:exists(S1_2189:exists(v_2186:S1_2258=union(S1_2265,
  {v_2262}) & v_2255<=v_2262 & v_2186=v_2262 & S1_2189=S1_2265 & v=v_2255 & 
  S1=union(S1_2258,{v_2255}) & S=union(S1_2189,{v_2186}) & 
  S!=()))))))) --> INS(S,S1,v),
 (exists(S1_2189:exists(v_2186:exists(S1_2297:exists(v_2294:S1_2239!=() & 
  v_2186=v_2294 & S1_2189=S_2214 & S1_2239=S1_2297 & (1+v_2294)<=v & 
  INS(S_2214,S1_2239,v) & S=union(S1_2189,{v_2186}) & S1=union(S1_2297,
  {v_2294}) & S!=()))))) --> INS(S,S1,v)]
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
                              EXISTS(flted_227_2519,
                              S2_2520: res::sll1<flted_227_2519,S2_2520>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=res]
                               [S<subset> S2_2520  & {v}<subset> S2_2520  & 
                                 S2_2520!=()]
                               [-1+flted_227_2519=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2435:exists(v_2432:S1_2435= & v_2432=v & S= & S2=union(S1_2435,
  {v_2432})))) --> INS2(S,S2,v),
 (exists(v_2449:exists(S1_2452:exists(S1_2445:exists(v_2442:exists(S1_2373:exists(v_2370:S1_2445=union(S1_2452,
  {v_2449}) & v_2442<=v_2449 & v_2370=v_2449 & S1_2373=S1_2452 & v=v_2442 & 
  S!=() & S2=union(S1_2445,{v_2442}) & S=union(S1_2373,
  {v_2370})))))))) --> INS2(S,S2,v),
 (exists(S1_2484:exists(v_2481:exists(S1_2373:exists(v_2370:S2_2428!=() & (1+
  v_2481)<=v_2402 & v_2370=v_2481 & S1_2373=S_2401 & S2_2428=S1_2484 & 
  v=v_2402 & INS2(S_2401,S2_2428,v_2402) & S2=union(S1_2484,{v_2481}) & 
  S!=() & S=union(S1_2373,{v_2370})))))) --> INS2(S,S2,v)]
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
                              EXISTS(n_2652,S_2653,n_2654,
                              S1_2655: x::sll1<n_2652,S_2653>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              res::sll1<n_2654,S1_2655>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([S=S_2653 & S=S1_2655]
                               [n=n_2652 & n=n_2654 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_81:S1= & S_81=S & S_81=)) --> CPY(S,S1),
 (exists(S_81:exists(S1_2579:exists(v_2576:exists(S1_2592:exists(v_2589:exists(S1_2547:exists(v_2544:S_81=union(S1_2579,
  {v_2576}) & S1_2579=S1_2547 & S_2551=S1_2547 & v_2589=v_2576 & 
  v_2544=v_2576 & S1_2571=S1_2592 & CPY(S_2551,S1_2571) & S1=union(S1_2592,
  {v_2589}) & S=union(S1_2547,{v_2544}) & S!=())))))))) --> CPY(S,S1),
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
                              EXISTS(m_2823,
                              S2_2824: res::sll1<m_2823,S2_2824>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([m_2823<=n & 0<=n][S2_2824<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2682:exists(v_2679:Anon_11=v & 
  v_2679=v & S1_2682=S_2704 & S2_2766=S2 & FIL(S_2704,S2_2766) & S!=() & 
  S=union(S1_2682,{v_2679})))))) --> FIL(S,S2),
 (exists(r_2775:exists(tmp_79':exists(x:exists(res:exists(m_2776:exists(m_2751:exists(n_2725:exists(n:exists(m:exists(v_bool_377_695':exists(v:exists(v_node_388_697':exists(v_bool_376_696':exists(m_2681:exists(S1_2682:exists(v_2679:exists(S1_2777:exists(v_2774:(r_2775=tmp_79' & 
  x=v_node_388_697' & res=v_node_388_697' & S2_2752=S1_2777 & 
  S1_2682=S_2726 & v_2679=v_2774 & 1+m_2776=m & 1+m_2751=m & n_2725=m_2681 & 
  -1+n=m_2681 & 0<=m & (-1+m)<=m_2681 & !(v_bool_377_695') & (1+v)<=v_2774 & 
  v_node_388_697'!=null & v_bool_376_696' & FIL(S_2726,S2_2752) & 
  0<=m_2681 | r_2775=tmp_79' & x=v_node_388_697' & res=v_node_388_697' & 
  S2_2752=S1_2777 & S1_2682=S_2726 & v_2679=v_2774 & 1+m_2776=m & 1+
  m_2751=m & n_2725=m_2681 & -1+n=m_2681 & 0<=m & (-1+m)<=m_2681 & 
  !(v_bool_377_695') & (1+v_2774)<=v & v_node_388_697'!=null & 
  v_bool_376_696' & FIL(S_2726,S2_2752) & 0<=m_2681) & S=union(S1_2682,
  {v_2679}) & S2=union(S1_2777,{v_2774}) & 
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
                              EXISTS(n_2911,
                              S2_2912: x::sll1<n_2911,S2_2912>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (([S1=S2_2912][n=n_2911 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2875:exists(v_2872:exists(S1_2852:exists(v_2849:v_2872=v_2849 & 
  S1_2852=S1_2856 & S2_2871=S1_2875 & TRAV(S1_2856,S2_2871) & 
  S2=union(S1_2875,{v_2872}) & S1!=() & S1=union(S1_2852,
  {v_2849})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_117_3068,
                              S3_3069: res::sll1<flted_117_3068,S3_3069>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([flted_117_3068=n1+n2 & 0<=n1 & 0<=n2]
                               [S1<subset> S3_3069 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_124_1011':exists(flted_117_116:exists(v_bool_119_1025':exists(x1:exists(x2:exists(v_bool_123_1024':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & n2<=-1 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' | res=x2 & 
  S2=S3 & n1=0 & v_node_124_1011'=x2 & flted_117_116=n2 & 
  v_bool_119_1025'<=0 & x1=null & x2!=null & 1<=v_bool_123_1024' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2975:exists(S:exists(S1_2949:exists(v_2946:S3_3030!=() & 
  S1_2975!=() & S1_2949!=() & {v_2946}<subset> S1_2975  & S<subset> S1_2975
   & S1_2992=S1_2975 & S1_2949=S2_2994 & S3_3030=S3 & S1=S & 
  MRG(S3_3030,S1_2992,S2_2994) & S2=union(S1_2949,{v_2946}) & S2!=() & 
  S1!=()))))) --> MRG(S3,S1,S2),
 (exists(S:exists(S1_2975:exists(S1_2949:exists(v_2946:S1_2975!=() & 
  S1_2949= & {v_2946}<subset> S1_2975  & S<subset> S1_2975  & S=S1 & 
  S3=S1_2975 & S2=union(S1_2949,{v_2946}) & S2!=() & 
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
                              EXISTS(flted_104_3124,
                              S2_3125: x'::sll1<flted_104_3124,S2_3125>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([1+flted_104_3124=m & 0<=m]
                               [S2_3125<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_119':exists(r_3091:exists(x':exists(x:exists(flted_104_118:exists(next_108_1040':exists(v_node_109_1041':exists(m_3092:exists(S1_3093:exists(v_3090:(-1+
  m=m_3092 & S1_3093=S2 & res=v_node_109_1041' & tmp_119'=v_node_109_1041' & 
  r_3091=x' & x=v_node_109_1041' & flted_104_118=m_3092 & m_3092<=-2 & 
  next_108_1040'=null & v_node_109_1041'!=null | -1+m=m_3092 & S1_3093=S2 & 
  res=v_node_109_1041' & tmp_119'=v_node_109_1041' & r_3091=x' & 
  x=v_node_109_1041' & flted_104_118=m_3092 & next_108_1040'=null & 
  v_node_109_1041'!=null & 0<=m_3092) & S1=union(S1_3093,{v_3090}) & 
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
                              EXISTS(k_3182,
                              S2_3183: x'::sll1<k_3182,S2_3183>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([null!=x']
                               [S<subset> S2_3183  & {v}<subset> S2_3183  & 
                                 S2_3183!=()]
                               [-1+k_3182=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S2_3173:exists(S_3155:exists(v_3156:S2_3173!=() & 
  {v_3156}<subset> S2_3173  & S_3155<subset> S2_3173  & S2_3173=S2 & 
  S=S_3155 & v_3156=v)))) --> SN(S,S2,v)]
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
                              EXISTS(n1_3579,n2_3580,S1_3581,
                              S2_3582: x'::sll1<n1_3579,S1_3581>@M[Orig][LHSCase]@ rem br[{390}] * 
                              res::sll1<n2_3580,S2_3582>@M[Orig][LHSCase]@ rem br[{390}]&
                              (
                              ([S1_3581!=() & S2_3582!=() & union(S1_3581,
                                 S2_3582)=S]
                               [null!=res][null!=x']
                               [0!=n1_3579 & 0<=n & n=n1_3579+n2_3580 & 
                                 0!=n2_3580]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3365:exists(v_3362:exists(S1_3447:exists(v_3444:S1_3365!=() & 
  S1_3447= & v_3362=v_3444 & S2=S1_3365 & S=union(S1_3365,{v_3362}) & 
  S1=union(S1_3447,{v_3444}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_333_755':exists(tmp_87':exists(xnext_3475:exists(m_3479:exists(m_3403:exists(a:exists(n:exists(n_3405:exists(n1_3471:exists(n2_3472:exists(x':exists(v_bool_322_756':exists(x:exists(res:exists(r_3478:exists(r_3402:exists(a_3476:exists(n1:exists(n2:exists(S1_3480:exists(v_3477:exists(S1_3404:exists(v_3401:S1_3473!=() & 
  S2_3474!=() & S1_3404!=() & (v_node_333_755'=res & tmp_87'=res & 
  xnext_3475=r_3478 & 1+m_3479=n1 & m_3403=-1+n1+n2 & -1+a=a_3476 & n=n1+
  n2 & n_3405=-1+n1+n2 & 1+n1_3471=n1 & n2_3472=n2 & S2_3474=S2 & 
  S1_3473=S1_3480 & S1_3404=S_3406 & v_3477=v_3401 & x'=x & n2<=-1 & 
  !(v_bool_322_756') & x!=null & res!=null & r_3478!=null & r_3402!=null & 
  1<=a_3476 & a_3476<=(-2+n1+n2) & SPLIT(S_3406,S1_3473,S2_3474) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3475=r_3478 & n1=0 & m_3479=-1 & 
  1+m_3403=n2 & -1+a=a_3476 & n=n2 & 1+n_3405=n2 & n1_3471=-1 & n2_3472=n2 & 
  S2_3474=S2 & S1_3473=S1_3480 & S1_3404=S_3406 & v_3477=v_3401 & x'=x & 
  1<=a_3476 & (2+a_3476)<=n2 & !(v_bool_322_756') & x!=null & res!=null & 
  r_3478!=null & r_3402!=null & SPLIT(S_3406,S1_3473,S2_3474) | 
  v_node_333_755'=res & tmp_87'=res & xnext_3475=r_3478 & 1+m_3479=n1 & 
  m_3403=-1+n1+n2 & -1+a=a_3476 & n=n1+n2 & n_3405=-1+n1+n2 & 1+n1_3471=n1 & 
  n2_3472=n2 & S2_3474=S2 & S1_3473=S1_3480 & S1_3404=S_3406 & 
  v_3477=v_3401 & x'=x & !(v_bool_322_756') & x!=null & res!=null & 
  r_3478!=null & r_3402!=null & 2<=n1 & 1<=a_3476 & a_3476<=(-2+n1+n2) & 
  SPLIT(S_3406,S1_3473,S2_3474) & 1<=n2) & S!=() & S1=union(S1_3480,
  {v_3477}) & S=union(S1_3404,
  {v_3401}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
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
                              EXISTS(m_3592,S3_3593,n_3594,
                              S4_3595: x'::sll1<m_3592,S3_3593>@M[Orig][LHSCase]@ rem br[{391,390}] * 
                              y'::sll1<n_3594,S4_3595>@M[Orig][LHSCase]@ rem br[{391,390}]&
                              (
                              ([m=m_3592 & 0<=m][n=n_3594 & 0<=n][S1=S4_3595]
                               [S2=S3_3593][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


16 false contexts at: ( (168,13)  (168,4)  (39,4)  (39,11)  (40,7)  (40,14)  (304,4)  (304,11)  (309,4)  (309,11)  (308,10)  (308,4)  (307,9)  (307,13)  (307,4)  (307,4) )

Total verification time: 8.1 second(s)
	Time spent in main process: 0.88 second(s)
	Time spent in child processes: 7.22 second(s)
