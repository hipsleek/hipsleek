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
                              or EXISTS(S_1563: x'::ll2<n_131,S4>@M[Orig][LHSCase]@ rem br[{405,404}]&
                                 (
                                 ([S4=S_1563 & 
                                    490::forall(_x:_x <notin> S_1563  | 
                                    _x=v) & S_1563!=()]
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
                              EXISTS(m_1785,
                              S1_1786: x::ll2<m_1785,S1_1786>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S1_1786<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1630:exists(S1_1633:exists(S1_1600:exists(v_1597:exists(S1_1712:exists(v_1709:S1_1600!=() & 
  S1_1600=union(S1_1633,{v_1630}) & S1_1712=S1_1633 & v_1597=v_1709 & 
  S=union(S1_1600,{v_1597}) & S1=union(S1_1712,{v_1709}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1665:exists(m_1666:exists(n_1679:exists(a:exists(m_1742:exists(m_1737:exists(v_int_209_1739:exists(n:exists(v_bool_205_936':exists(x:exists(r_1741:exists(m:exists(S1_1743:exists(v_1740:exists(S1_1667:exists(v_1664:S1_1667!=() & 
  S1_1738!=() & (r_1665=r_1741 & S1_1738=S1_1743 & S1_1667=S_1680 & 
  v_1740=v_1664 & 1+m_1666=n & 1+n_1679=n & -1+a=v_int_209_1739 & m=0 & 
  m_1742=-1 & m_1737=-1 & 1<=v_int_209_1739 & (2+v_int_209_1739)<=n & 
  !(v_bool_205_936') & x!=null & r_1741!=null & DEL(S_1680,S1_1738) | 
  r_1665=r_1741 & S1_1738=S1_1743 & S1_1667=S_1680 & v_1740=v_1664 & 1+
  m_1666=n & 1+n_1679=n & -1+a=v_int_209_1739 & 1+m_1742=m & 1+m_1737=m & 
  1<=v_int_209_1739 & (2+v_int_209_1739)<=n & !(v_bool_205_936') & x!=null & 
  r_1741!=null & DEL(S_1680,S1_1738) & 2<=m) & S!=() & S1=union(S1_1743,
  {v_1740}) & S=union(S1_1667,{v_1664})))))))))))))))))) --> DEL(S,S1)]
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
                              EXISTS(m_1935,
                              S1_1936: res::ll2<m_1935,S1_1936>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([m_1935<=n & 0<=n]
                               [S1_1936=S & a <notin> S  | S1_1936<subset> S
                                  & a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> DEL2(a,S,S1),
 (exists(n:exists(r_1812:exists(res:exists(v_node_223_901':exists(m:exists(v_bool_220_911':exists(x:exists(v_bool_223_910':exists(m_1813:exists(S1_1814:exists(v_1811:(v_1811=a & 
  S1_1814=S1 & -1+n=m_1813 & r_1812=v_node_223_901' & res=v_node_223_901' & 
  m=m_1813 & m_1813<=-2 & v_bool_220_911'<=0 & x!=null & 
  1<=v_bool_223_910' | v_1811=a & S1_1814=S1 & -1+n=m_1813 & 
  r_1812=v_node_223_901' & res=v_node_223_901' & m=m_1813 & 
  v_bool_220_911'<=0 & x!=null & 1<=v_bool_223_910' & 0<=m_1813) & S!=() & 
  S=union(S1_1814,{v_1811}))))))))))))) --> DEL2(a,S,S1),
 (exists(r_1881:exists(v_node_224_1879:exists(m_1882:exists(m_1877:exists(n:exists(n_1839:exists(v_node_224_909':exists(m:exists(v_bool_220_911':exists(v_bool_223_910':exists(x:exists(res:exists(m_1813:exists(S1_1883:exists(v_1880:exists(S1_1814:exists(v_1811:(r_1881=v_node_224_1879 & 
  S1_1878=S1_1883 & S_1840=S1_1814 & v_1811=v_1880 & 1+m_1882=m & 1+
  m_1877=m & -1+n=m_1813 & n_1839=m_1813 & v_node_224_909'=res & 0<=m & (-1+
  m)<=m_1813 & !(v_bool_220_911') & !(v_bool_223_910') & (1+a)<=v_1880 & 
  x!=null & res!=null & 0<=m_1813 & DEL2(a,S_1840,S1_1878) | 
  r_1881=v_node_224_1879 & S1_1878=S1_1883 & S_1840=S1_1814 & 
  v_1811=v_1880 & 1+m_1882=m & 1+m_1877=m & -1+n=m_1813 & n_1839=m_1813 & 
  v_node_224_909'=res & 0<=m & (-1+m)<=m_1813 & !(v_bool_220_911') & 
  !(v_bool_223_910') & (1+v_1880)<=a & x!=null & res!=null & 0<=m_1813 & 
  DEL2(a,S_1840,S1_1878)) & S1=union(S1_1883,{v_1880}) & S=union(S1_1814,
  {v_1811}) & S!=())))))))))))))))))) --> DEL2(a,S,S1)]
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
                              or EXISTS(Anon_2086,
                                 m_2087: res::node<m_2087,Anon_2086>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_2087 & m_2087 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_22:exists(r_2011:exists(v_node_403_704':exists(m_2012:exists(v:exists(v_bool_399_710':exists(x:exists(v_bool_402_709':exists(n:exists(S1_2013:exists(v_2010:(res=x & 
  Anon_22=r_2011 & m=v_2010 & v_node_403_704'=x & 1+m_2012=n & n<=-1 & (1+
  v)<=v_2010 & v_bool_399_710'<=0 & x!=null & 1<=v_bool_402_709' | res=x & 
  Anon_22=r_2011 & m=v_2010 & v_node_403_704'=x & 1+m_2012=n & (1+
  v)<=v_2010 & v_bool_399_710'<=0 & x!=null & 1<=v_bool_402_709' & 1<=n) & 
  S!=() & S=union(S1_2013,{v_2010})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2013:exists(v_2010:v_2010<=v & S1_2013=S_2036 & 
  m_2067=m & (1+v)<=m & FGE(S_2036,m_2067) & S=union(S1_2013,{v_2010}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              EXISTS(flted_138_2160,flted_138_2161,S1_2162,
                              S2_2163: x'::ll2<flted_138_2161,S1_2162>@M[Orig][LHSCase]@ rem br[{404}] * 
                              res::ll2<flted_138_2160,S2_2163>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S1_2162!=() & union(S1_2162,S2_2163)=S]
                               [null!=x'][1+flted_138_2160=n & 0<=n]
                               [1=flted_138_2161]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_123':exists(res:exists(r_2112:exists(v_node_142_1040':exists(n:exists(flted_138_122:exists(m_2126:exists(r_2125:exists(x:exists(flted_138_121:exists(next_141_1039':exists(x':exists(m_2113:exists(S1_2127:exists(v_2124:exists(S1_2114:exists(v_2111:S1_2127= & 
  (tmp_123'=v_node_142_1040' & res=v_node_142_1040' & 
  r_2112=v_node_142_1040' & -1+n=m_2113 & flted_138_122=1 & m_2126=0 & 
  v_2124=v_2111 & S1_2114=S2 & r_2125=next_141_1039' & x=x' & 
  flted_138_121=m_2113 & next_141_1039'=null & m_2113<=-2 & x'!=null | 
  tmp_123'=v_node_142_1040' & res=v_node_142_1040' & 
  r_2112=v_node_142_1040' & -1+n=m_2113 & flted_138_122=1 & m_2126=0 & 
  v_2124=v_2111 & S1_2114=S2 & r_2125=next_141_1039' & x=x' & 
  flted_138_121=m_2113 & next_141_1039'=null & x'!=null & 0<=m_2113) & 
  S!=() & S1=union(S1_2127,{v_2124}) & S=union(S1_2114,
  {v_2111}))))))))))))))))))) --> GN(S,S1,S2)]
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
                              EXISTS(flted_178_2235,
                              S2_2236: res::ll2<flted_178_2235,S2_2236>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([2+flted_178_2235=n & 0<=n]
                               [S2_2236<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2213:exists(S1_2216:exists(S1_2185:exists(v_2182:S1_2185=union(S1_2216,
  {v_2213}) & S1_2185!=() & S2=S1_2216 & S!=() & S=union(S1_2185,
  {v_2182})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
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
                              EXISTS(flted_188_2352,
                              S1_2353: x::ll2<flted_188_2352,S1_2353>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_2353!=() & S1_2353=union(S,{a})][null!=x]
                               [-1+flted_188_2352=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2305:exists(v_2302:exists(S1_2298:exists(v_2295:exists(S1_2260:exists(v_2257:S1_2305= & 
  S1_2298=union(S1_2305,{v_2302}) & S1_2260= & v_2257=v_2295 & v_2302=a & 
  S1=union(S1_2298,{v_2295}) & S=union(S1_2260,{v_2257}) & 
  S!=()))))))) --> INS(S,S1,a),
 (exists(S1_2324:exists(v_2321:exists(S1_2260:exists(v_2257:S1_2260!=() & 
  S1_2320!=() & v_2321=v_2257 & S1_2260=S_2280 & S1_2320=S1_2324 & 
  INS(S_2280,S1_2320,a) & S!=() & S1=union(S1_2324,{v_2321}) & 
  S=union(S1_2260,{v_2257})))))) --> INS(S,S1,a)]
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
                              EXISTS(n_2485,S_2486,n_2487,
                              S2_2488: x::ll2<n_2485,S_2486>@M[Orig][LHSCase]@ rem br[{405,404}] * 
                              res::ll2<n_2487,S2_2488>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S=S_2486 & S=S2_2488]
                               [n=n_2485 & n=n_2487 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S_94=S & S_94=)) --> CPY(S,S2),
 (exists(S_94:exists(S1_2412:exists(v_2409:exists(S1_2425:exists(v_2422:exists(S1_2380:exists(v_2377:S_94=union(S1_2412,
  {v_2409}) & S1_2412=S1_2380 & S_2384=S1_2380 & v_2422=v_2409 & 
  v_2377=v_2409 & S2_2404=S1_2425 & CPY(S_2384,S2_2404) & S2=union(S1_2425,
  {v_2422}) & S=union(S1_2380,{v_2377}) & S!=())))))))) --> CPY(S,S2),
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
                              EXISTS(m_2656,
                              S2_2657: res::ll2<m_2656,S2_2657>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([m_2656<=n & 0<=n][S2_2657<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2515:exists(v_2512:Anon_11=v & 
  v_2512=v & S1_2515=S_2537 & S2_2599=S2 & FIL(S_2537,S2_2599) & S!=() & 
  S=union(S1_2515,{v_2512})))))) --> FIL(S,S2),
 (exists(r_2608:exists(tmp_90':exists(x:exists(res:exists(m_2609:exists(m_2584:exists(n_2558:exists(n:exists(m:exists(v_bool_373_731':exists(v:exists(v_node_386_733':exists(v_bool_372_732':exists(m_2514:exists(S1_2515:exists(v_2512:exists(S1_2610:exists(v_2607:(r_2608=tmp_90' & 
  x=v_node_386_733' & res=v_node_386_733' & S2_2585=S1_2610 & 
  S1_2515=S_2559 & v_2512=v_2607 & 1+m_2609=m & 1+m_2584=m & n_2558=m_2514 & 
  -1+n=m_2514 & 0<=m & (-1+m)<=m_2514 & !(v_bool_373_731') & (1+v)<=v_2607 & 
  v_node_386_733'!=null & v_bool_372_732' & FIL(S_2559,S2_2585) & 
  0<=m_2514 | r_2608=tmp_90' & x=v_node_386_733' & res=v_node_386_733' & 
  S2_2585=S1_2610 & S1_2515=S_2559 & v_2512=v_2607 & 1+m_2609=m & 1+
  m_2584=m & n_2558=m_2514 & -1+n=m_2514 & 0<=m & (-1+m)<=m_2514 & 
  !(v_bool_373_731') & (1+v_2607)<=v & v_node_386_733'!=null & 
  v_bool_372_732' & FIL(S_2559,S2_2585) & 0<=m_2514) & S=union(S1_2515,
  {v_2512}) & S2=union(S1_2610,{v_2607}) & 
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
                              EXISTS(m_3030,
                              S2_3031: res::ll2<m_3030,S2_3031>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([m_3030<=n & 0<=n][S2_3031<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(v:exists(Anon_11:exists(Anon_12:exists(r_2899:exists(v_node_361_756':exists(res:exists(m:exists(tmp_91':exists(v_bool_350_754':exists(x:exists(v_bool_349_755':exists(m_2900:exists(S1_2901:exists(v_2898:(-1+
  n=m_2900 & S1_2901=S2 & v_2898=Anon_11 & v=Anon_11 & Anon_12=res & 
  r_2899=res & v_node_361_756'=res & m=m_2900 & m_2900<=-2 & tmp_91'=null & 
  1<=v_bool_350_754' & x!=null & 1<=v_bool_349_755' | -1+n=m_2900 & 
  S1_2901=S2 & v_2898=Anon_11 & v=Anon_11 & Anon_12=res & r_2899=res & 
  v_node_361_756'=res & m=m_2900 & tmp_91'=null & 1<=v_bool_350_754' & 
  x!=null & 1<=v_bool_349_755' & 0<=m_2900) & S!=() & S=union(S1_2901,
  {v_2898}))))))))))))))))) --> RMV2(S,S2),
 (exists(r_2968:exists(tmp_91':exists(x:exists(res:exists(m_2969:exists(m_2952:exists(n_2926:exists(n:exists(m:exists(v_bool_350_754':exists(v:exists(v_node_361_756':exists(v_bool_349_755':exists(m_2900:exists(S1_2901:exists(v_2898:exists(S1_2970:exists(v_2967:(r_2968=tmp_91' & 
  x=v_node_361_756' & res=v_node_361_756' & S2_2953=S1_2970 & 
  S1_2901=S_2927 & v_2898=v_2967 & 1+m_2969=m & 1+m_2952=m & n_2926=m_2900 & 
  -1+n=m_2900 & 0<=m & (-1+m)<=m_2900 & !(v_bool_350_754') & (1+v)<=v_2967 & 
  v_node_361_756'!=null & v_bool_349_755' & RMV2(S_2927,S2_2953) & 
  0<=m_2900 | r_2968=tmp_91' & x=v_node_361_756' & res=v_node_361_756' & 
  S2_2953=S1_2970 & S1_2901=S_2927 & v_2898=v_2967 & 1+m_2969=m & 1+
  m_2952=m & n_2926=m_2900 & -1+n=m_2900 & 0<=m & (-1+m)<=m_2900 & 
  !(v_bool_350_754') & (1+v_2967)<=v & v_node_361_756'!=null & 
  v_bool_349_755' & RMV2(S_2927,S2_2953) & 0<=m_2900) & S=union(S1_2901,
  {v_2898}) & S2=union(S1_2970,{v_2967}) & 
  S!=()))))))))))))))))))) --> RMV2(S,S2),
 (S2= & S=) --> RMV2(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
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
                              EXISTS(n_3118,
                              S2_3119: x::ll2<n_3118,S2_3119>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (([S1=S2_3119][n=n_3118 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_3082:exists(v_3079:exists(S1_3059:exists(v_3056:v_3079=v_3056 & 
  S1_3059=S1_3063 & S2_3078=S1_3082 & TRAV(S1_3063,S2_3078) & 
  S2=union(S1_3082,{v_3079}) & S1!=() & S1=union(S1_3059,
  {v_3056})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_102_3174,
                              S2_3175: x'::ll2<flted_102_3174,S2_3175>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([1+flted_102_3174=m & 0<=m]
                               [S2_3175<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_127':exists(r_3141:exists(x':exists(x:exists(flted_102_126:exists(next_106_1086':exists(v_node_107_1087':exists(m_3142:exists(S1_3143:exists(v_3140:(-1+
  m=m_3142 & S1_3143=S2 & res=v_node_107_1087' & tmp_127'=v_node_107_1087' & 
  r_3141=x' & x=v_node_107_1087' & flted_102_126=m_3142 & m_3142<=-2 & 
  next_106_1086'=null & v_node_107_1087'!=null | -1+m=m_3142 & S1_3143=S2 & 
  res=v_node_107_1087' & tmp_127'=v_node_107_1087' & r_3141=x' & 
  x=v_node_107_1087' & flted_102_126=m_3142 & next_106_1086'=null & 
  v_node_107_1087'!=null & 0<=m_3142) & S1=union(S1_3143,{v_3140}) & 
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
                              EXISTS(flted_91_3193,
                              S1_3194: x'::ll2<flted_91_3193,S1_3194>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_3194!=() & S1_3194=union(S,{v})][null!=x']
                               [-1+flted_91_3193=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3181:exists(v_3178:v=v_3178 & S1_3181=S & S1=union(S1_3181,
  {v_3178})))) --> PUF(S1,S,v)]
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
                              EXISTS(flted_255_3300,
                              S_3301: ys'::ll2<flted_255_3300,S_3301>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S_3301=union(S1,S2)][xs'=null]
                               [flted_255_3300=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3248:exists(S1_3251:exists(S1_3229:exists(v_3226:S2_3242=union(S1_3251,
  {v_3248}) & S_3278!=() & v_3248=v_3226 & S1_3229=S1_3240 & S_3278=S & 
  S2=S1_3251 & REV(S_3278,S1_3240,S2_3242) & S1=union(S1_3229,{v_3226}) & 
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
                              EXISTS(k_3320,S2_3321: true&(
                              ([S2_3321!=() & S2_3321=union(S,{v})][null!=x]
                               [-1+k_3320=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3308:exists(v_3305:v=v_3305 & S1_3308=S & S2=union(S1_3308,
  {v_3305})))) --> SN(S,S2,v)]
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
                              EXISTS(flted_415_3670,
                              S_3671: x'::ll2<flted_415_3670,S_3671>@M[Orig][LHSCase]@ rem br[{405,404}]&
                              (
                              ([S_3671=union(S1,S2)]
                               [flted_415_3670=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> SPI(S,S1,S2),
 (exists(v_3608:exists(S1_3611:exists(S1_3604:exists(v_3601:exists(S1_3541:exists(v_3538:exists(S1_3510:exists(v_3507:S1_3604=union(S1_3611,
  {v_3608}) & S2_3552=S1_3541 & S1_3510=S1_3550 & v_3507=v_3601 & 
  v_3538=v_3608 & S_3590=S1_3611 & SPI(S_3590,S1_3550,S2_3552) & S1!=() & 
  S=union(S1_3604,{v_3601}) & S2!=() & S2=union(S1_3541,{v_3538}) & 
  S1=union(S1_3510,{v_3507})))))))))) --> SPI(S,S1,S2),
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
                              EXISTS(n2_3909,n1_3910,S1_3911,
                              S2_3912: x'::ll2<n1_3910,S1_3911>@M[Orig][LHSCase]@ rem br[{404}] * 
                              res::ll2<n2_3909,S2_3912>@M[Orig][LHSCase]@ rem br[{404}]&
                              (
                              ([S1_3911!=() & S2_3912!=() & union(S1_3911,
                                 S2_3912)=S]
                               [null!=res][null!=x']
                               [a=n1_3910 & 0!=n1_3910 & 0<=n & n=n1_3910+
                                 n2_3909 & 0!=n2_3909]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3786:exists(v_3783:exists(S1_3706:exists(v_3703:S1_3706!=() & 
  S1_3786= & v_3783=v_3703 & S1_3706=S2 & S1=union(S1_3786,{v_3783}) & 
  S!=() & S=union(S1_3706,{v_3703})))))) --> SPLIT(S,S1,S2),
 (exists(S1_3822:exists(v_3819:exists(S1_3745:exists(v_3742:S1_3745!=() & 
  S2_3816!=() & S1_3815!=() & v_3819=v_3742 & S1_3745=S_3747 & 
  S1_3815=S1_3822 & S2_3816=S2 & SPLIT(S_3747,S1_3815,S2_3816) & 
  S1=union(S1_3822,{v_3819}) & S=union(S1_3745,{v_3742}) & 
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

Total verification time: 8.44 second(s)
	Time spent in main process: 2.33 second(s)
	Time spent in child processes: 6.11 second(s)
