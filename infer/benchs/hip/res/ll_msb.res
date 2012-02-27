/usr/local/bin/mona

Processing file "ll_msb.ss"
Parsing ll_msb.ss ...
Parsing ../../../prelude.ss ...
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
                              
                              x'::ll2<n_131,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S4=][null=x'][0=n][0=n_131][0<=m]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(S_1567: x'::ll2<n_131,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                 (
                                 ([S4=S_1567 & 
                                    490::forall(_x:_x <notin> S_1567  | 
                                    _x=v) & S_1567!=()]
                                  [n=n_131 & 1<=n][x'!=null][0<=m]))&
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
                              EXISTS(m_1789,
                              S1_1790: x::ll2<m_1789,S1_1790>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S1_1790<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1634:exists(S1_1637:exists(S1_1604:exists(v_1601:exists(S1_1716:exists(v_1713:S1_1604!=() & 
  S1_1604=union(S1_1637,{v_1634}) & S1_1716=S1_1637 & v_1601=v_1713 & 
  S=union(S1_1604,{v_1601}) & S1=union(S1_1716,{v_1713}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1669:exists(m_1670:exists(n_1683:exists(a:exists(m_1746:exists(m_1741:exists(v_int_209_1743:exists(n:exists(v_bool_205_936':exists(x:exists(r_1745:exists(m:exists(S1_1747:exists(v_1744:exists(S1_1671:exists(v_1668:S1_1671!=() & 
  S1_1742!=() & (r_1669=r_1745 & S1_1742=S1_1747 & S1_1671=S_1684 & 
  v_1744=v_1668 & 1+m_1670=n & 1+n_1683=n & -1+a=v_int_209_1743 & m=0 & 
  m_1746=-1 & m_1741=-1 & 1<=v_int_209_1743 & (2+v_int_209_1743)<=n & 
  !(v_bool_205_936') & x!=null & r_1745!=null & DEL(S_1684,S1_1742) | 
  r_1669=r_1745 & S1_1742=S1_1747 & S1_1671=S_1684 & v_1744=v_1668 & 1+
  m_1670=n & 1+n_1683=n & -1+a=v_int_209_1743 & 1+m_1746=m & 1+m_1741=m & 
  1<=v_int_209_1743 & (2+v_int_209_1743)<=n & !(v_bool_205_936') & x!=null & 
  r_1745!=null & DEL(S_1684,S1_1742) & 2<=m) & S!=() & S1=union(S1_1747,
  {v_1744}) & S=union(S1_1671,{v_1668})))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL2(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  a <notin> S  | a <in> S 
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
                    EBase true&(([MayLoop][a <notin> S  | a <in> S ]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(m_1939,
                              S1_1940: res::ll2<m_1939,S1_1940>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([m_1939<=n & 0<=n]
                               [S1_1940=S & a <notin> S  | S1_1940<subset> S
                                  & a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> DEL2(a,S,S1),
 (exists(n:exists(r_1816:exists(res:exists(v_node_223_901':exists(m:exists(v_bool_220_911':exists(x:exists(v_bool_223_910':exists(m_1817:exists(S1_1818:exists(v_1815:(v_1815=a & 
  S1_1818=S1 & -1+n=m_1817 & r_1816=v_node_223_901' & res=v_node_223_901' & 
  m=m_1817 & m_1817<=-2 & v_bool_220_911'<=0 & x!=null & 
  1<=v_bool_223_910' | v_1815=a & S1_1818=S1 & -1+n=m_1817 & 
  r_1816=v_node_223_901' & res=v_node_223_901' & m=m_1817 & 
  v_bool_220_911'<=0 & x!=null & 1<=v_bool_223_910' & 0<=m_1817) & S!=() & 
  S=union(S1_1818,{v_1815}))))))))))))) --> DEL2(a,S,S1),
 (exists(r_1885:exists(v_node_224_1883:exists(m_1886:exists(m_1881:exists(n:exists(n_1843:exists(v_node_224_909':exists(m:exists(v_bool_220_911':exists(v_bool_223_910':exists(x:exists(res:exists(m_1817:exists(S1_1887:exists(v_1884:exists(S1_1818:exists(v_1815:(r_1885=v_node_224_1883 & 
  S1_1882=S1_1887 & S_1844=S1_1818 & v_1815=v_1884 & 1+m_1886=m & 1+
  m_1881=m & -1+n=m_1817 & n_1843=m_1817 & v_node_224_909'=res & 0<=m & (-1+
  m)<=m_1817 & !(v_bool_220_911') & !(v_bool_223_910') & (1+a)<=v_1884 & 
  x!=null & res!=null & 0<=m_1817 & DEL2(a,S_1844,S1_1882) | 
  r_1885=v_node_224_1883 & S1_1882=S1_1887 & S_1844=S1_1818 & 
  v_1815=v_1884 & 1+m_1886=m & 1+m_1881=m & -1+n=m_1817 & n_1843=m_1817 & 
  v_node_224_909'=res & 0<=m & (-1+m)<=m_1817 & !(v_bool_220_911') & 
  !(v_bool_223_910') & (1+v_1884)<=a & x!=null & res!=null & 0<=m_1817 & 
  DEL2(a,S_1844,S1_1882)) & S1=union(S1_1887,{v_1884}) & S=union(S1_1818,
  {v_1815}) & S!=())))))))))))))))))) --> DEL2(a,S,S1)]
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
                              or EXISTS(Anon_2091,
                                 m_2092: res::node<m_2092,Anon_2091>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_2092 & m_2092 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_22:exists(r_2015:exists(v_node_403_704':exists(m_2016:exists(v:exists(v_bool_399_710':exists(x:exists(v_bool_402_709':exists(n:exists(S1_2017:exists(v_2014:(res=x & 
  Anon_22=r_2015 & m=v_2014 & v_node_403_704'=x & 1+m_2016=n & n<=-1 & (1+
  v)<=v_2014 & v_bool_399_710'<=0 & x!=null & 1<=v_bool_402_709' | res=x & 
  Anon_22=r_2015 & m=v_2014 & v_node_403_704'=x & 1+m_2016=n & (1+
  v)<=v_2014 & v_bool_399_710'<=0 & x!=null & 1<=v_bool_402_709' & 1<=n) & 
  S!=() & S=union(S1_2017,{v_2014})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2017:exists(v_2014:v_2014<=v & S1_2017=S_2040 & 
  m_2071=m & (1+v)<=m & FGE(S_2040,m_2071) & S=union(S1_2017,{v_2014}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
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
                              EXISTS(flted_138_2165,flted_138_2166,S1_2167,
                              S2_2168: x'::ll2<flted_138_2166,S1_2167>@M[Orig][LHSCase]@ rem br[{404}] * 
                              res::ll2<flted_138_2165,S2_2168>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S1_2167!=() & union(S1_2167,S2_2168)=S]
                               [null!=x'][1+flted_138_2165=n & 0<=n]
                               [1=flted_138_2166]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_123':exists(res:exists(r_2117:exists(v_node_142_1040':exists(n:exists(flted_138_122:exists(m_2131:exists(r_2130:exists(x:exists(flted_138_121:exists(next_141_1039':exists(x':exists(m_2118:exists(S1_2132:exists(v_2129:exists(S1_2119:exists(v_2116:S1_2132= & 
  (tmp_123'=v_node_142_1040' & res=v_node_142_1040' & 
  r_2117=v_node_142_1040' & -1+n=m_2118 & flted_138_122=1 & m_2131=0 & 
  v_2129=v_2116 & S1_2119=S2 & r_2130=next_141_1039' & x=x' & 
  flted_138_121=m_2118 & next_141_1039'=null & m_2118<=-2 & x'!=null | 
  tmp_123'=v_node_142_1040' & res=v_node_142_1040' & 
  r_2117=v_node_142_1040' & -1+n=m_2118 & flted_138_122=1 & m_2131=0 & 
  v_2129=v_2116 & S1_2119=S2 & r_2130=next_141_1039' & x=x' & 
  flted_138_121=m_2118 & next_141_1039'=null & x'!=null & 0<=m_2118) & 
  S!=() & S1=union(S1_2132,{v_2129}) & S=union(S1_2119,
  {v_2116}))))))))))))))))))) --> GN(S,S1,S2)]
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
                              EXISTS(flted_178_2240,
                              S2_2241: res::ll2<flted_178_2240,S2_2241>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([2+flted_178_2240=n & 0<=n]
                               [S2_2241<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2218:exists(S1_2221:exists(S1_2190:exists(v_2187:S1_2190=union(S1_2221,
  {v_2218}) & S1_2190!=() & S2=S1_2221 & S!=() & S=union(S1_2190,
  {v_2187})))))) --> GNN(S,S2)]
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
                              EXISTS(flted_188_2357,
                              S1_2358: x::ll2<flted_188_2357,S1_2358>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_2358!=() & S1_2358=union(S,{a})][null!=x]
                               [-1+flted_188_2357=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2310:exists(v_2307:exists(S1_2303:exists(v_2300:exists(S1_2265:exists(v_2262:S1_2310= & 
  S1_2303=union(S1_2310,{v_2307}) & S1_2265= & v_2262=v_2300 & v_2307=a & 
  S1=union(S1_2303,{v_2300}) & S=union(S1_2265,{v_2262}) & 
  S!=()))))))) --> INS(S,S1,a),
 (exists(S1_2329:exists(v_2326:exists(S1_2265:exists(v_2262:S1_2265!=() & 
  S1_2325!=() & v_2326=v_2262 & S1_2265=S_2285 & S1_2325=S1_2329 & 
  INS(S_2285,S1_2325,a) & S!=() & S1=union(S1_2329,{v_2326}) & 
  S=union(S1_2265,{v_2262})))))) --> INS(S,S1,a)]
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
                              EXISTS(n_2490,S_2491,n_2492,
                              S2_2493: x::ll2<n_2490,S_2491>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                              res::ll2<n_2492,S2_2493>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S=S_2491 & S=S2_2493]
                               [n=n_2490 & n=n_2492 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S_94=S & S_94=)) --> CPY(S,S2),
 (exists(S_94:exists(S1_2417:exists(v_2414:exists(S1_2430:exists(v_2427:exists(S1_2385:exists(v_2382:S_94=union(S1_2417,
  {v_2414}) & S1_2417=S1_2385 & S_2389=S1_2385 & v_2427=v_2414 & 
  v_2382=v_2414 & S2_2409=S1_2430 & CPY(S_2389,S2_2409) & S2=union(S1_2430,
  {v_2427}) & S=union(S1_2385,{v_2382}) & S!=())))))))) --> CPY(S,S2),
 (exists(S_94:S_94= & S=S_94 & S2=)) --> CPY(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
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
                              EXISTS(m_2661,
                              S2_2662: res::ll2<m_2661,S2_2662>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([m_2661<=n & 0<=n][S2_2662<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2520:exists(v_2517:Anon_11=v & 
  v_2517=v & S1_2520=S_2542 & S2_2604=S2 & FIL(S_2542,S2_2604) & S!=() & 
  S=union(S1_2520,{v_2517})))))) --> FIL(S,S2),
 (exists(r_2613:exists(tmp_90':exists(x:exists(res:exists(m_2614:exists(m_2589:exists(n_2563:exists(n:exists(m:exists(v_bool_373_731':exists(v:exists(v_node_386_733':exists(v_bool_372_732':exists(m_2519:exists(S1_2520:exists(v_2517:exists(S1_2615:exists(v_2612:(r_2613=tmp_90' & 
  x=v_node_386_733' & res=v_node_386_733' & S2_2590=S1_2615 & 
  S1_2520=S_2564 & v_2517=v_2612 & 1+m_2614=m & 1+m_2589=m & n_2563=m_2519 & 
  -1+n=m_2519 & 0<=m & (-1+m)<=m_2519 & !(v_bool_373_731') & (1+v)<=v_2612 & 
  v_node_386_733'!=null & v_bool_372_732' & FIL(S_2564,S2_2590) & 
  0<=m_2519 | r_2613=tmp_90' & x=v_node_386_733' & res=v_node_386_733' & 
  S2_2590=S1_2615 & S1_2520=S_2564 & v_2517=v_2612 & 1+m_2614=m & 1+
  m_2589=m & n_2563=m_2519 & -1+n=m_2519 & 0<=m & (-1+m)<=m_2519 & 
  !(v_bool_373_731') & (1+v_2612)<=v & v_node_386_733'!=null & 
  v_bool_372_732' & FIL(S_2564,S2_2590) & 0<=m_2519) & S=union(S1_2520,
  {v_2517}) & S2=union(S1_2615,{v_2612}) & 
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
                              EXISTS(m_3035,
                              S2_3036: res::ll2<m_3035,S2_3036>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([m_3035<=n & 0<=n][S2_3036<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(v:exists(Anon_11:exists(Anon_12:exists(r_2904:exists(v_node_361_756':exists(res:exists(m:exists(tmp_91':exists(v_bool_350_754':exists(x:exists(v_bool_349_755':exists(m_2905:exists(S1_2906:exists(v_2903:(-1+
  n=m_2905 & S1_2906=S2 & v_2903=Anon_11 & v=Anon_11 & Anon_12=res & 
  r_2904=res & v_node_361_756'=res & m=m_2905 & m_2905<=-2 & tmp_91'=null & 
  1<=v_bool_350_754' & x!=null & 1<=v_bool_349_755' | -1+n=m_2905 & 
  S1_2906=S2 & v_2903=Anon_11 & v=Anon_11 & Anon_12=res & r_2904=res & 
  v_node_361_756'=res & m=m_2905 & tmp_91'=null & 1<=v_bool_350_754' & 
  x!=null & 1<=v_bool_349_755' & 0<=m_2905) & S!=() & S=union(S1_2906,
  {v_2903}))))))))))))))))) --> RMV2(S,S2),
 (exists(r_2973:exists(tmp_91':exists(x:exists(res:exists(m_2974:exists(m_2957:exists(n_2931:exists(n:exists(m:exists(v_bool_350_754':exists(v:exists(v_node_361_756':exists(v_bool_349_755':exists(m_2905:exists(S1_2906:exists(v_2903:exists(S1_2975:exists(v_2972:(r_2973=tmp_91' & 
  x=v_node_361_756' & res=v_node_361_756' & S2_2958=S1_2975 & 
  S1_2906=S_2932 & v_2903=v_2972 & 1+m_2974=m & 1+m_2957=m & n_2931=m_2905 & 
  -1+n=m_2905 & 0<=m & (-1+m)<=m_2905 & !(v_bool_350_754') & (1+v)<=v_2972 & 
  v_node_361_756'!=null & v_bool_349_755' & RMV2(S_2932,S2_2958) & 
  0<=m_2905 | r_2973=tmp_91' & x=v_node_361_756' & res=v_node_361_756' & 
  S2_2958=S1_2975 & S1_2906=S_2932 & v_2903=v_2972 & 1+m_2974=m & 1+
  m_2957=m & n_2931=m_2905 & -1+n=m_2905 & 0<=m & (-1+m)<=m_2905 & 
  !(v_bool_350_754') & (1+v_2972)<=v & v_node_361_756'!=null & 
  v_bool_349_755' & RMV2(S_2932,S2_2958) & 0<=m_2905) & S=union(S1_2906,
  {v_2903}) & S2=union(S1_2975,{v_2972}) & 
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
                              EXISTS(n_3123,
                              S2_3124: x::ll2<n_3123,S2_3124>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S1=S2_3124][n=n_3123 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_3087:exists(v_3084:exists(S1_3064:exists(v_3061:v_3084=v_3061 & 
  S1_3064=S1_3068 & S2_3083=S1_3087 & TRAV(S1_3068,S2_3083) & 
  S2=union(S1_3087,{v_3084}) & S1!=() & S1=union(S1_3064,
  {v_3061})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_102_3179,
                              S2_3180: x'::ll2<flted_102_3179,S2_3180>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([1+flted_102_3179=m & 0<=m]
                               [S2_3180<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_127':exists(r_3146:exists(x':exists(x:exists(flted_102_126:exists(next_106_1086':exists(v_node_107_1087':exists(m_3147:exists(S1_3148:exists(v_3145:(-1+
  m=m_3147 & S1_3148=S2 & res=v_node_107_1087' & tmp_127'=v_node_107_1087' & 
  r_3146=x' & x=v_node_107_1087' & flted_102_126=m_3147 & m_3147<=-2 & 
  next_106_1086'=null & v_node_107_1087'!=null | -1+m=m_3147 & S1_3148=S2 & 
  res=v_node_107_1087' & tmp_127'=v_node_107_1087' & r_3146=x' & 
  x=v_node_107_1087' & flted_102_126=m_3147 & next_106_1086'=null & 
  v_node_107_1087'!=null & 0<=m_3147) & S1=union(S1_3148,{v_3145}) & 
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
                              EXISTS(flted_91_3198,
                              S1_3199: x'::ll2<flted_91_3198,S1_3199>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_3199!=() & S1_3199=union(S,{v})][null!=x']
                               [-1+flted_91_3198=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3186:exists(v_3183:v=v_3183 & S1_3186=S & S1=union(S1_3186,
  {v_3183})))) --> PUF(S1,S,v)]
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
                              x::ll2<n_124,S2>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([x=res][S1=S2][n_124=n & 0<=n]))&
                              {FLOW,(20,21)=__norm})
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
                              EXISTS(flted_255_3306,
                              S_3307: ys'::ll2<flted_255_3306,S_3307>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S_3307=union(S1,S2)][xs'=null]
                               [flted_255_3306=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3253:exists(S1_3256:exists(S1_3234:exists(v_3231:S2_3247=union(S1_3256,
  {v_3253}) & S_3283!=() & v_3253=v_3231 & S1_3234=S1_3245 & S_3283=S & 
  S2=S1_3256 & REV(S_3283,S1_3245,S2_3247) & S1=union(S1_3234,{v_3231}) & 
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
                              EXISTS(k_3326,S2_3327: true&(
                              ([S2_3327!=() & S2_3327=union(S,{v})][null!=x]
                               [-1+k_3326=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3314:exists(v_3311:v=v_3311 & S1_3314=S & S2=union(S1_3314,
  {v_3311})))) --> SN(S,S2,v)]
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
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure size$node SUCCESS

Checking procedure splice$node~node... 
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
                              EXISTS(flted_415_3676,
                              S_3677: x'::ll2<flted_415_3676,S_3677>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S_3677=union(S1,S2)]
                               [flted_415_3676=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> SPI(S,S1,S2),
 (exists(v_3614:exists(S1_3617:exists(S1_3610:exists(v_3607:exists(S1_3547:exists(v_3544:exists(S1_3516:exists(v_3513:S1_3610=union(S1_3617,
  {v_3614}) & S2_3558=S1_3547 & S1_3516=S1_3556 & v_3513=v_3607 & 
  v_3544=v_3614 & S_3596=S1_3617 & SPI(S_3596,S1_3556,S2_3558) & S1!=() & 
  S=union(S1_3610,{v_3607}) & S2!=() & S2=union(S1_3547,{v_3544}) & 
  S1=union(S1_3516,{v_3513})))))))))) --> SPI(S,S1,S2),
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
                              EXISTS(n2_3915,n1_3916,S1_3917,
                              S2_3918: x'::ll2<n1_3916,S1_3917>@M[Orig][LHSCase]@ rem br[{404}] * 
                              res::ll2<n2_3915,S2_3918>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_3917!=() & S2_3918!=() & union(S1_3917,
                                 S2_3918)=S]
                               [null!=res][null!=x']
                               [a=n1_3916 & 0!=n1_3916 & 0<=n & n=n1_3916+
                                 n2_3915 & 0!=n2_3915]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3792:exists(v_3789:exists(S1_3712:exists(v_3709:S1_3712!=() & 
  S1_3792= & v_3789=v_3709 & S1_3712=S2 & S1=union(S1_3792,{v_3789}) & 
  S!=() & S=union(S1_3712,{v_3709})))))) --> SPLIT(S,S1,S2),
 (exists(S1_3828:exists(v_3825:exists(S1_3751:exists(v_3748:S1_3751!=() & 
  S2_3822!=() & S1_3821!=() & v_3825=v_3748 & S1_3751=S_3753 & 
  S1_3821=S1_3828 & S2_3822=S2 & SPLIT(S_3753,S1_3821,S2_3822) & 
  S1=union(S1_3828,{v_3825}) & S=union(S1_3751,{v_3748}) & 
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
                              x'::ll2<m_132,S3>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                              y'::ll2<n_133,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([x=y'][x'=y][S2=S3][S1=S4][n_133=n & 0<=n]
                               [m_132=m & 0<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (162,13)  (162,4)  (241,4)  (241,11)  (246,4)  (246,11)  (245,10)  (245,4)  (244,8)  (244,12)  (244,4)  (244,4) )

Total verification time: 5.97 second(s)
	Time spent in main process: 2.54 second(s)
	Time spent in child processes: 3.43 second(s)
