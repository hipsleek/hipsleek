/usr/local/bin/mona

Processing file "ll_msb.ss"
Parsing ll_msb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure append$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
Starting Omega...oc

!!! REL :  APP(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[n1; S1; n2; 
                    S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase]@ rem br[{404}] * 
                    y::ll2<n2,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([null!=x][0!=n1][S1!=()][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(m,
                                S: x::ll2<m,S>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([m=n1+n2][APP(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase]@ rem br[{404}] * 
                  y::ll2<n2,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ([S1!=()][(n1+1)<=0 & x!=null | x!=null & 1<=n1]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              EXISTS(m_1441,
                              S_1442: x::ll2<m_1441,S_1442>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([union(S1,S2)=S_1442]
                               [m_1441=n1+n2 & 0<=n1 & 0<=n2]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1391:exists(v_1388:exists(S1_1349:exists(v_1346:S1_1349= & 
  v_1346=v_1388 & S1_1391=S2 & S=union(S1_1391,{v_1388}) & S1!=() & 
  S1=union(S1_1349,{v_1346})))))) --> APP(S,S1,S2),
 (exists(S1_1412:exists(v_1409:exists(S1_1349:exists(v_1346:S_1408!=() & 
  S1_1349!=() & S1_1349=S1_1368 & v_1346=v_1409 & S_1408=S1_1412 & 
  S2_1370=S2 & APP(S_1408,S1_1368,S2_1370) & S=union(S1_1412,{v_1409}) & 
  S1=union(S1_1349,{v_1346}) & S1!=()))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

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
                                                       EAssume 48::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 49::
                                                         EXISTS(n_108,
                                                         S: res::ll2<n_108,S>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                                         (
                                                         ([CL(S,v)][n=n_108]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 50::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(())&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 48::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 49::
                                                       EXISTS(n_1541,
                                                       S_1542: res::ll2<n_1541,S_1542>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                                       (
                                                       ([n=n_1541 & 1<=n]
                                                        [forall(_x:_x <notin> S_1542
                                                           | _x=v)]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 50::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_1495:exists(v_1492:S1_1495= & v_1492=v & S=union(S1_1495,
  {v_1492})))) --> CL(S,v),
 (exists(S1_1512:exists(v_1509:S_1507!=() & S1_1512=S_1507 & v=v_1509 & 
  CL(S_1507,v) & S=union(S1_1512,{v_1509})))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_131,
                                S4: x'::ll2<n_131,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([n=n_131]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              EXISTS(n_1564,S4_1565: true&(
                              ([S4_1565=][null=x'][0=n_1564][0=n][0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(S_1566: x'::ll2<n_131,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                 (
                                 ([S4=S_1566 & 
                                    490::forall(_x:_x <notin> S_1566  | 
                                    _x=v) & S_1566!=()]
                                  [x'!=null][n=n_131 & 1<=n][0<=m]))&
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(m,
                                S1: x::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([DEL(S,S1)][true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(m_1788,
                              S1_1789: x::ll2<m_1788,S1_1789>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S1_1789<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1633:exists(S1_1636:exists(S1_1603:exists(v_1600:exists(S1_1715:exists(v_1712:S1_1603!=() & 
  S1_1603=union(S1_1636,{v_1633}) & S1_1715=S1_1636 & v_1600=v_1712 & 
  S=union(S1_1603,{v_1600}) & S1=union(S1_1715,{v_1712}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1668:exists(m_1669:exists(n_1682:exists(a:exists(m_1745:exists(m_1740:exists(v_int_209_1742:exists(n:exists(v_bool_205_936':exists(x:exists(r_1744:exists(m:exists(S1_1746:exists(v_1743:exists(S1_1670:exists(v_1667:S1_1670!=() & 
  S1_1741!=() & (r_1668=r_1744 & S1_1741=S1_1746 & S1_1670=S_1683 & 
  v_1743=v_1667 & 1+m_1669=n & 1+n_1682=n & -1+a=v_int_209_1742 & m=0 & 
  m_1745=-1 & m_1740=-1 & 1<=v_int_209_1742 & (2+v_int_209_1742)<=n & 
  !(v_bool_205_936') & x!=null & r_1744!=null & DEL(S_1683,S1_1741) | 
  r_1668=r_1744 & S1_1741=S1_1746 & S1_1670=S_1683 & v_1743=v_1667 & 1+
  m_1669=n & 1+n_1682=n & -1+a=v_int_209_1742 & 1+m_1745=m & 1+m_1740=m & 
  1<=v_int_209_1742 & (2+v_int_209_1742)<=n & !(v_bool_205_936') & x!=null & 
  r_1744!=null & DEL(S_1683,S1_1741) & 2<=m) & S!=() & S1=union(S1_1746,
  {v_1743}) & S=union(S1_1670,{v_1667})))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL2(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(m,
                                S1: res::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([m<=n][DEL2(a,S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(m_1938,
                              S1_1939: res::ll2<m_1938,S1_1939>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([m_1938<=n & 0<=n]
                               [S1_1939=S & a <notin> S  | S1_1939<subset> S
                                  & a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> DEL2(a,S,S1),
 (exists(n:exists(r_1815:exists(res:exists(v_node_223_901':exists(m:exists(v_bool_220_911':exists(x:exists(v_bool_223_910':exists(m_1816:exists(S1_1817:exists(v_1814:(v_1814=a & 
  S1_1817=S1 & -1+n=m_1816 & r_1815=v_node_223_901' & res=v_node_223_901' & 
  m=m_1816 & m_1816<=-2 & v_bool_220_911'<=0 & x!=null & 
  1<=v_bool_223_910' | v_1814=a & S1_1817=S1 & -1+n=m_1816 & 
  r_1815=v_node_223_901' & res=v_node_223_901' & m=m_1816 & 
  v_bool_220_911'<=0 & x!=null & 1<=v_bool_223_910' & 0<=m_1816) & S!=() & 
  S=union(S1_1817,{v_1814}))))))))))))) --> DEL2(a,S,S1),
 (exists(r_1884:exists(v_node_224_1882:exists(m_1885:exists(m_1880:exists(n:exists(n_1842:exists(v_node_224_909':exists(m:exists(v_bool_220_911':exists(v_bool_223_910':exists(x:exists(res:exists(m_1816:exists(S1_1886:exists(v_1883:exists(S1_1817:exists(v_1814:(r_1884=v_node_224_1882 & 
  S1_1881=S1_1886 & S_1843=S1_1817 & v_1814=v_1883 & 1+m_1885=m & 1+
  m_1880=m & -1+n=m_1816 & n_1842=m_1816 & v_node_224_909'=res & 0<=m & (-1+
  m)<=m_1816 & !(v_bool_220_911') & !(v_bool_223_910') & (1+a)<=v_1883 & 
  x!=null & res!=null & 0<=m_1816 & DEL2(a,S_1843,S1_1881) | 
  r_1884=v_node_224_1882 & S1_1881=S1_1886 & S_1843=S1_1817 & 
  v_1814=v_1883 & 1+m_1885=m & 1+m_1880=m & -1+n=m_1816 & n_1842=m_1816 & 
  v_node_224_909'=res & 0<=m & (-1+m)<=m_1816 & !(v_bool_220_911') & 
  !(v_bool_223_910') & (1+v_1883)<=a & x!=null & res!=null & 0<=m_1816 & 
  DEL2(a,S_1843,S1_1881)) & S1=union(S1_1886,{v_1883}) & S=union(S1_1817,
  {v_1814}) & S!=())))))))))))))))))) --> DEL2(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 93::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_22,
                                   m: res::node<m,Anon_22>@M[Orig][]&(
                                   ([FGE(S,m) & (1+v)<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 93::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_2090,
                                 m_2091: res::node<m_2091,Anon_2090>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_2091 & m_2091 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_22:exists(r_2014:exists(v_node_403_704':exists(m_2015:exists(v:exists(v_bool_399_710':exists(x:exists(v_bool_402_709':exists(n:exists(S1_2016:exists(v_2013:(res=x & 
  Anon_22=r_2014 & m=v_2013 & v_node_403_704'=x & 1+m_2015=n & n<=-1 & (1+
  v)<=v_2013 & v_bool_399_710'<=0 & x!=null & 1<=v_bool_402_709' | res=x & 
  Anon_22=r_2014 & m=v_2013 & v_node_403_704'=x & 1+m_2015=n & (1+
  v)<=v_2013 & v_bool_399_710'<=0 & x!=null & 1<=v_bool_402_709' & 1<=n) & 
  S!=() & S=union(S1_2016,{v_2013})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2016:exists(v_2013:v_2013<=v & S1_2016=S_2039 & 
  m_2070=m & (1+v)<=m & FGE(S_2039,m_2070) & S=union(S1_2016,{v_2013}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::ref [x]
                                EXISTS(flted_138_121,flted_138_122,S1,
                                S2: x'::ll2<flted_138_122,S1>@M[Orig][LHSCase]@ rem br[{404}] * 
                                res::ll2<flted_138_121,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (
                                ([1=flted_138_122][1+flted_138_121=n]
                                 [S1!=() & GN(S,S1,S2)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 27::ref [x]
                              EXISTS(flted_138_2164,flted_138_2165,S1_2166,
                              S2_2167: x'::ll2<flted_138_2165,S1_2166>@M[Orig][LHSCase]@ rem br[{404}] * 
                              res::ll2<flted_138_2164,S2_2167>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S1_2166!=() & union(S1_2166,S2_2167)=S]
                               [null!=x'][1+flted_138_2164=n & 0<=n]
                               [1=flted_138_2165]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_123':exists(res:exists(r_2116:exists(v_node_142_1040':exists(n:exists(flted_138_122:exists(m_2130:exists(r_2129:exists(x:exists(flted_138_121:exists(next_141_1039':exists(x':exists(m_2117:exists(S1_2131:exists(v_2128:exists(S1_2118:exists(v_2115:S1_2131= & 
  (tmp_123'=v_node_142_1040' & res=v_node_142_1040' & 
  r_2116=v_node_142_1040' & -1+n=m_2117 & flted_138_122=1 & m_2130=0 & 
  v_2128=v_2115 & S1_2118=S2 & r_2129=next_141_1039' & x=x' & 
  flted_138_121=m_2117 & next_141_1039'=null & m_2117<=-2 & x'!=null | 
  tmp_123'=v_node_142_1040' & res=v_node_142_1040' & 
  r_2116=v_node_142_1040' & -1+n=m_2117 & flted_138_122=1 & m_2130=0 & 
  v_2128=v_2115 & S1_2118=S2 & r_2129=next_141_1039' & x=x' & 
  flted_138_121=m_2117 & next_141_1039'=null & x'!=null & 0<=m_2117) & 
  S!=() & S1=union(S1_2131,{v_2128}) & S=union(S1_2118,
  {v_2115}))))))))))))))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                    ([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(flted_178_114,
                                S2: res::ll2<flted_178_114,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([2+flted_178_114=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              EXISTS(flted_178_2239,
                              S2_2240: res::ll2<flted_178_2239,S2_2240>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([2+flted_178_2239=n & 0<=n]
                               [S2_2240<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2217:exists(S1_2220:exists(S1_2189:exists(v_2186:S1_2189=union(S1_2220,
  {v_2217}) & S1_2189!=() & S2=S1_2220 & S!=() & S=union(S1_2189,
  {v_2186})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INS(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                    ([0!=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_188_111,
                                S1: x::ll2<flted_188_111,S1>@M[Orig][LHSCase]@ rem br[{404}]&
                                (
                                ([-1+flted_188_111=n][S1!=() & INS(S,S1,a)]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_188_2356,
                              S1_2357: x::ll2<flted_188_2356,S1_2357>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_2357!=() & S1_2357=union(S,{a})][null!=x]
                               [-1+flted_188_2356=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2309:exists(v_2306:exists(S1_2302:exists(v_2299:exists(S1_2264:exists(v_2261:S1_2309= & 
  S1_2302=union(S1_2309,{v_2306}) & S1_2264= & v_2261=v_2299 & v_2306=a & 
  S1=union(S1_2302,{v_2299}) & S=union(S1_2264,{v_2261}) & 
  S!=()))))))) --> INS(S,S1,a),
 (exists(S1_2328:exists(v_2325:exists(S1_2264:exists(v_2261:S1_2264!=() & 
  S1_2324!=() & v_2325=v_2261 & S1_2264=S_2284 & S1_2324=S1_2328 & 
  INS(S_2284,S1_2324,a) & S!=() & S1=union(S1_2328,{v_2325}) & 
  S=union(S1_2264,{v_2261})))))) --> INS(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(S,S2)
!!! POST:  S2=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 71::
                                EXISTS(n_93,S_94,n_95,
                                S2: x::ll2<n_93,S_94>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                                res::ll2<n_95,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([S=S_94 & CPY(S,S2)][n=n_95 & n=n_93]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 71::
                              EXISTS(n_2489,S_2490,n_2491,
                              S2_2492: x::ll2<n_2489,S_2490>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                              res::ll2<n_2491,S2_2492>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S=S_2490 & S=S2_2492]
                               [n=n_2489 & n=n_2491 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S_94=S & S_94=)) --> CPY(S,S2),
 (exists(S_94:exists(S1_2416:exists(v_2413:exists(S1_2429:exists(v_2426:exists(S1_2384:exists(v_2381:S_94=union(S1_2416,
  {v_2413}) & S1_2416=S1_2384 & S_2388=S1_2384 & v_2426=v_2413 & 
  v_2381=v_2413 & S2_2408=S1_2429 & CPY(S_2388,S2_2408) & S2=union(S1_2429,
  {v_2426}) & S=union(S1_2384,{v_2381}) & S!=())))))))) --> CPY(S,S2),
 (exists(S_94:S_94= & S=S_94 & S2=)) --> CPY(S,S2)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::
                                EXISTS(m,
                                S2: res::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([m<=n][FIL(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 85::
                              EXISTS(m_2660,
                              S2_2661: res::ll2<m_2660,S2_2661>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([m_2660<=n & 0<=n][S2_2661<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2519:exists(v_2516:Anon_11=v & 
  v_2516=v & S1_2519=S_2541 & S2_2603=S2 & FIL(S_2541,S2_2603) & S!=() & 
  S=union(S1_2519,{v_2516})))))) --> FIL(S,S2),
 (exists(r_2612:exists(tmp_90':exists(x:exists(res:exists(m_2613:exists(m_2588:exists(n_2562:exists(n:exists(m:exists(v_bool_373_731':exists(v:exists(v_node_386_733':exists(v_bool_372_732':exists(m_2518:exists(S1_2519:exists(v_2516:exists(S1_2614:exists(v_2611:(r_2612=tmp_90' & 
  x=v_node_386_733' & res=v_node_386_733' & S2_2589=S1_2614 & 
  S1_2519=S_2563 & v_2516=v_2611 & 1+m_2613=m & 1+m_2588=m & n_2562=m_2518 & 
  -1+n=m_2518 & 0<=m & (-1+m)<=m_2518 & !(v_bool_373_731') & (1+v)<=v_2611 & 
  v_node_386_733'!=null & v_bool_372_732' & FIL(S_2563,S2_2589) & 
  0<=m_2518 | r_2612=tmp_90' & x=v_node_386_733' & res=v_node_386_733' & 
  S2_2589=S1_2614 & S1_2519=S_2563 & v_2516=v_2611 & 1+m_2613=m & 1+
  m_2588=m & n_2562=m_2518 & -1+n=m_2518 & 0<=m & (-1+m)<=m_2518 & 
  !(v_bool_373_731') & (1+v_2611)<=v & v_node_386_733'!=null & 
  v_bool_372_732' & FIL(S_2563,S2_2589) & 0<=m_2518) & S=union(S1_2519,
  {v_2516}) & S2=union(S1_2614,{v_2611}) & 
  S!=()))))))))))))))))))) --> FIL(S,S2),
 (S2= & S=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RMV2(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 78::
                                EXISTS(m,
                                S2: res::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([m<=n][RMV2(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 78::
                              EXISTS(m_3034,
                              S2_3035: res::ll2<m_3034,S2_3035>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([m_3034<=n & 0<=n][S2_3035<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(v:exists(Anon_11:exists(Anon_12:exists(r_2903:exists(v_node_361_756':exists(res:exists(m:exists(tmp_91':exists(v_bool_350_754':exists(x:exists(v_bool_349_755':exists(m_2904:exists(S1_2905:exists(v_2902:(-1+
  n=m_2904 & S1_2905=S2 & v_2902=Anon_11 & v=Anon_11 & Anon_12=res & 
  r_2903=res & v_node_361_756'=res & m=m_2904 & m_2904<=-2 & tmp_91'=null & 
  1<=v_bool_350_754' & x!=null & 1<=v_bool_349_755' | -1+n=m_2904 & 
  S1_2905=S2 & v_2902=Anon_11 & v=Anon_11 & Anon_12=res & r_2903=res & 
  v_node_361_756'=res & m=m_2904 & tmp_91'=null & 1<=v_bool_350_754' & 
  x!=null & 1<=v_bool_349_755' & 0<=m_2904) & S!=() & S=union(S1_2905,
  {v_2902}))))))))))))))))) --> RMV2(S,S2),
 (exists(r_2972:exists(tmp_91':exists(x:exists(res:exists(m_2973:exists(m_2956:exists(n_2930:exists(n:exists(m:exists(v_bool_350_754':exists(v:exists(v_node_361_756':exists(v_bool_349_755':exists(m_2904:exists(S1_2905:exists(v_2902:exists(S1_2974:exists(v_2971:(r_2972=tmp_91' & 
  x=v_node_361_756' & res=v_node_361_756' & S2_2957=S1_2974 & 
  S1_2905=S_2931 & v_2902=v_2971 & 1+m_2973=m & 1+m_2956=m & n_2930=m_2904 & 
  -1+n=m_2904 & 0<=m & (-1+m)<=m_2904 & !(v_bool_350_754') & (1+v)<=v_2971 & 
  v_node_361_756'!=null & v_bool_349_755' & RMV2(S_2931,S2_2957) & 
  0<=m_2904 | r_2972=tmp_91' & x=v_node_361_756' & res=v_node_361_756' & 
  S2_2957=S1_2974 & S1_2905=S_2931 & v_2902=v_2971 & 1+m_2973=m & 1+
  m_2956=m & n_2930=m_2904 & -1+n=m_2904 & 0<=m & (-1+m)<=m_2904 & 
  !(v_bool_350_754') & (1+v_2971)<=v & v_node_361_756'!=null & 
  v_bool_349_755' & RMV2(S_2931,S2_2957) & 0<=m_2904) & S=union(S1_2905,
  {v_2902}) & S2=union(S1_2974,{v_2971}) & 
  S!=()))))))))))))))))))) --> RMV2(S,S2),
 (S2= & S=) --> RMV2(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 68::
                                EXISTS(n_97,
                                S2: x::ll2<n_97,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([TRAV(S1,S2)][n=n_97]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 68::
                              EXISTS(n_3122,
                              S2_3123: x::ll2<n_3122,S2_3123>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S1=S2_3123][n=n_3122 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_3086:exists(v_3083:exists(S1_3063:exists(v_3060:v_3083=v_3060 & 
  S1_3063=S1_3067 & S2_3082=S1_3086 & TRAV(S1_3067,S2_3082) & 
  S2=union(S1_3086,{v_3083}) & S1!=() & S1=union(S1_3063,
  {v_3060})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; 
                    S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{404}]&(
                    ([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(flted_102_126,
                                S2: x'::ll2<flted_102_126,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([1+flted_102_126=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{404}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(flted_102_3178,
                              S2_3179: x'::ll2<flted_102_3178,S2_3179>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([1+flted_102_3178=m & 0<=m]
                               [S2_3179<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_127':exists(r_3145:exists(x':exists(x:exists(flted_102_126:exists(next_106_1086':exists(v_node_107_1087':exists(m_3146:exists(S1_3147:exists(v_3144:(-1+
  m=m_3146 & S1_3147=S2 & res=v_node_107_1087' & tmp_127'=v_node_107_1087' & 
  r_3145=x' & x=v_node_107_1087' & flted_102_126=m_3146 & m_3146<=-2 & 
  next_106_1086'=null & v_node_107_1087'!=null | -1+m=m_3146 & S1_3147=S2 & 
  res=v_node_107_1087' & tmp_127'=v_node_107_1087' & r_3145=x' & 
  x=v_node_107_1087' & flted_102_126=m_3146 & next_106_1086'=null & 
  v_node_107_1087'!=null & 0<=m_3146) & S1=union(S1_3147,{v_3144}) & 
  S1!=()))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(S1,S,v)
!!! POST:  S1=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_91_129,
                                S1: x'::ll2<flted_91_129,S1>@M[Orig][LHSCase]@ rem br[{404}]&
                                (
                                ([-1+flted_91_129=n][S1!=() & PUF(S1,S,v)]
                                 [null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(flted_91_3197,
                              S1_3198: x'::ll2<flted_91_3197,S1_3198>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_3198!=() & S1_3198=union(S,{v})][null!=x']
                               [-1+flted_91_3197=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3185:exists(v_3182:v=v_3182 & S1_3185=S & S1=union(S1_3185,
  {v_3182})))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(n_124,
                                S2: x::ll2<n_124,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([n=n_124]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              EXISTS(n_3203,
                              S2_3204: x::ll2<n_3203,S2_3204>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([n=n_3203 & 0<=n][S1=S2_3204][res=x]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
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
                    S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                    ys::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 55::ref [xs;ys]
                                EXISTS(flted_255_106,
                                S: ys'::ll2<flted_255_106,S>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (
                                ([flted_255_106=m+n][null=xs'][REV(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                  ys::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 55::ref [xs;ys]
                              EXISTS(flted_255_3307,
                              S_3308: ys'::ll2<flted_255_3307,S_3308>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S_3308=union(S1,S2)][xs'=null]
                               [flted_255_3307=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3254:exists(S1_3257:exists(S1_3235:exists(v_3232:S2_3248=union(S1_3257,
  {v_3254}) & S_3284!=() & v_3254=v_3232 & S1_3235=S1_3246 & S_3284=S & 
  S2=S1_3257 & REV(S_3284,S1_3246,S2_3248) & S1=union(S1_3235,{v_3232}) & 
  S1!=()))))) --> REV(S,S1,S2),
 (S=S2 & S1=) --> REV(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(S,S2,v)
!!! POST:  S2=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                    S](ex)x::node<v,t>@M[Orig][] * 
                    t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                    y::ll2<j,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([x!=null][0<=Anon_16][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(k,
                                S2: x::ll2<k,S2>@M[Orig][LHSCase]@ rem br[{404}]&
                                (([-1+k=j][S2!=() & SN(S,S2,v)][null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig][] * 
                  t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                  y::ll2<j,S>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                  ([x!=null][0<=Anon_16]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              EXISTS(k_3327,S2_3328: true&(
                              ([S2_3328!=() & S2_3328=union(S,{v})][null!=x]
                               [-1+k_3327=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3315:exists(v_3312:v=v_3312 & S1_3315=S & S2=union(S1_3315,
  {v_3312})))) --> SN(S,S2,v)]
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
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPI]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 96::ref [x]
                                EXISTS(flted_415_87,
                                S: x'::ll2<flted_415_87,S>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([flted_415_87=m+n][SPI(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 96::ref [x]
                              EXISTS(flted_415_3677,
                              S_3678: x'::ll2<flted_415_3677,S_3678>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S_3678=union(S1,S2)]
                               [flted_415_3677=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> SPI(S,S1,S2),
 (exists(v_3615:exists(S1_3618:exists(S1_3611:exists(v_3608:exists(S1_3548:exists(v_3545:exists(S1_3517:exists(v_3514:S1_3611=union(S1_3618,
  {v_3615}) & S2_3559=S1_3548 & S1_3517=S1_3557 & v_3514=v_3608 & 
  v_3545=v_3615 & S_3597=S1_3618 & SPI(S_3597,S1_3557,S2_3559) & S1!=() & 
  S=union(S1_3611,{v_3608}) & S2!=() & S2=union(S1_3548,{v_3545}) & 
  S1=union(S1_3517,{v_3514})))))))))) --> SPI(S,S1,S2),
 (exists(m:exists(x:exists(flted_415_87:exists(v_bool_420_687':exists(y:exists(v_bool_417_688':exists(x':exists(n:(S1=S & 
  m=0 & x=x' & flted_415_87=n & n<=-1 & v_bool_420_687'<=0 & y=null & 
  v_bool_417_688'<=0 & x'!=null | S1=S & m=0 & x=x' & flted_415_87=n & 
  v_bool_420_687'<=0 & y=null & v_bool_417_688'<=0 & x'!=null & 1<=n) & 
  S1!=() & S2=))))))))) --> SPI(S,S1,S2)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [x]
                                EXISTS(n2,n1,S1,
                                S2: x'::ll2<n1,S1>@M[Orig][LHSCase]@ rem br[{404}] * 
                                res::ll2<n2,S2>@M[Orig][LHSCase]@ rem br[{404}]&
                                (
                                ([a=n1 & 0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][null!=x']
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{404}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [x]
                              EXISTS(n2_3916,n1_3917,S1_3918,
                              S2_3919: x'::ll2<n1_3917,S1_3918>@M[Orig][LHSCase]@ rem br[{404}] * 
                              res::ll2<n2_3916,S2_3919>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_3918!=() & S2_3919!=() & union(S1_3918,
                                 S2_3919)=S]
                               [null!=res][null!=x']
                               [a=n1_3917 & 0!=n1_3917 & 0<=n & n=n1_3917+
                                 n2_3916 & 0!=n2_3916]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3793:exists(v_3790:exists(S1_3713:exists(v_3710:S1_3713!=() & 
  S1_3793= & v_3790=v_3710 & S1_3713=S2 & S1=union(S1_3793,{v_3790}) & 
  S!=() & S=union(S1_3713,{v_3710})))))) --> SPLIT(S,S1,S2),
 (exists(S1_3829:exists(v_3826:exists(S1_3752:exists(v_3749:S1_3752!=() & 
  S2_3823!=() & S1_3822!=() & v_3826=v_3749 & S1_3752=S_3754 & 
  S1_3822=S1_3829 & S2_3823=S2 & SPLIT(S_3754,S1_3822,S2_3823) & 
  S1=union(S1_3829,{v_3826}) & S=union(S1_3752,{v_3749}) & 
  S!=()))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_132,n_133,S3,
                                S4: x'::ll2<m_132,S3>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                                y'::ll2<n_133,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                (([m=m_132][n=n_133]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(m_3929,S3_3930,n_3931,
                              S4_3932: x'::ll2<m_3929,S3_3930>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                              y'::ll2<n_3931,S4_3932>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([m=m_3929 & 0<=m][n=n_3931 & 0<=n][S1=S4_3932]
                               [S2=S3_3930][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (162,13)  (162,4)  (241,4)  (241,11)  (246,4)  (246,11)  (245,10)  (245,4)  (244,8)  (244,12)  (244,4)  (244,4) )

Total verification time: 3.92 second(s)
	Time spent in main process: 0.55 second(s)
	Time spent in child processes: 3.37 second(s)
