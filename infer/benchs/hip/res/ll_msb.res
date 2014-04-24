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
                    S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase]@ rem br[{409}] * 
                    y::ll2<n2,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([null!=x][0!=n1][S1!=()][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 25::
                                EXISTS(m,
                                S: x::ll2<m,S>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([m=n1+n2][APP(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase]@ rem br[{409}] * 
                  y::ll2<n2,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ([S1!=()][(n1+1)<=0 & x!=null | x!=null & 1<=n1]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 25::
                              EXISTS(m_1456,
                              S_1457: x::ll2<m_1456,S_1457>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([union(S1,S2)=S_1457]
                               [m_1456=n1+n2 & 0<=n1 & 0<=n2]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1414:exists(v_1411:exists(S1_1372:exists(v_1369:S1_1372= & 
  v_1369=v_1411 & S1_1414=S2 & S=union(S1_1414,{v_1411}) & S1!=() & 
  S1=union(S1_1372,{v_1369})))))) --> APP(S,S1,S2),
 (exists(S1_1433:exists(v_1430:exists(S1_1372:exists(v_1369:S_1429!=() & 
  S1_1372!=() & S1_1372=S1_1391 & v_1369=v_1430 & S_1429=S1_1433 & 
  S2_1393=S2 & APP(S_1429,S1_1391,S2_1393) & S=union(S1_1433,{v_1430}) & 
  S1=union(S1_1372,{v_1369}) & S1!=()))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure assign$node~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 16::ref [x]
                                                         true&(([null=x']))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 17::ref [x]
                                                         EXISTS(n_132,
                                                         S4: x'::ll2<n_132,S4>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                                         (([n=n_132]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 18::ref [x]
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 16::ref [x]
                                                       true&(
                                                       ([null=x'][0=n][0<=m]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 17::ref [x]
                                                       EXISTS(S_1479: 
                                                       x'::ll2<n_132,S4>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                                       (
                                                       ([S4=S_1479 & 
                                                          467::forall(x_1471:x_1471 <notin> S_1479
                                                           | x_1471=v) & 
                                                          S_1479!=()]
                                                        [x'!=null]
                                                        [n=n_132 & 1<=n]
                                                        [0<=m]))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 18::ref [x]
                                                       true&(
                                                       ([0<=m][n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
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
                                                       EAssume 53::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 54::
                                                         EXISTS(n_108,
                                                         S: res::ll2<n_108,S>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                                         (
                                                         ([CL(S,v)][n=n_108]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 55::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(())&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 53::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 54::
                                                       EXISTS(n_1575,
                                                       S_1576: res::ll2<n_1575,S_1576>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                                       (
                                                       ([n=n_1575 & 1<=n]
                                                        [forall(_x:_x <notin> S_1576
                                                           | _x=v)]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 55::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_1532:exists(v_1529:S1_1532= & v_1529=v & S=union(S1_1532,
  {v_1529})))) --> CL(S,v),
 (exists(S1_1549:exists(v_1546:S_1544!=() & S1_1549=S_1544 & v=v_1546 & 
  CL(S_1544,v) & S=union(S1_1549,{v_1546})))) --> CL(S,v)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::
                                EXISTS(m,
                                S1: x::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([DEL(S,S1)][true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 43::
                              EXISTS(m_1783,
                              S1_1784: x::ll2<m_1783,S1_1784>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([S1_1784<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1643:exists(S1_1646:exists(S1_1613:exists(v_1610:exists(S1_1725:exists(v_1722:S1_1613!=() & 
  S1_1613=union(S1_1646,{v_1643}) & S1_1725=S1_1646 & v_1610=v_1722 & 
  S=union(S1_1613,{v_1610}) & S1=union(S1_1725,{v_1722}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1678:exists(m_1679:exists(n_1692:exists(a:exists(m_1752:exists(m_1747:exists(v_int_213_1749:exists(n:exists(v_bool_209_952':exists(x:exists(r_1751:exists(m:exists(S1_1753:exists(v_1750:exists(S1_1680:exists(v_1677:S1_1680!=() & 
  S1_1748!=() & (r_1678=r_1751 & S1_1748=S1_1753 & S1_1680=S_1693 & 
  v_1750=v_1677 & 1+m_1679=n & 1+n_1692=n & -1+a=v_int_213_1749 & m=0 & 
  m_1752=-1 & m_1747=-1 & 1<=v_int_213_1749 & (2+v_int_213_1749)<=n & 
  !(v_bool_209_952') & x!=null & r_1751!=null & DEL(S_1693,S1_1748) | 
  r_1678=r_1751 & S1_1748=S1_1753 & S1_1680=S_1693 & v_1750=v_1677 & 1+
  m_1679=n & 1+n_1692=n & -1+a=v_int_213_1749 & 1+m_1752=m & 1+m_1747=m & 
  1<=v_int_213_1749 & (2+v_int_213_1749)<=n & !(v_bool_209_952') & x!=null & 
  r_1751!=null & DEL(S_1693,S1_1748) & 2<=m) & S!=() & S1=union(S1_1753,
  {v_1750}) & S=union(S1_1680,{v_1677})))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(m,
                                S1: res::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([m<=n][DEL2(a,S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(m_1923,
                              S1_1924: res::ll2<m_1923,S1_1924>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([m_1923<=n & 0<=n]
                               [S1_1924=S & a <notin> S  | S1_1924<subset> S
                                  & a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> DEL2(a,S,S1),
 (exists(n:exists(r_1810:exists(res:exists(v_node_227_917':exists(m:exists(v_bool_224_927':exists(x:exists(v_bool_227_926':exists(m_1811:exists(S1_1812:exists(v_1809:(v_1809=a & 
  S1_1812=S1 & -1+n=m_1811 & r_1810=v_node_227_917' & res=v_node_227_917' & 
  m=m_1811 & m_1811<=-2 & v_bool_224_927'<=0 & x!=null & 
  1<=v_bool_227_926' | v_1809=a & S1_1812=S1 & -1+n=m_1811 & 
  r_1810=v_node_227_917' & res=v_node_227_917' & m=m_1811 & 
  v_bool_224_927'<=0 & x!=null & 1<=v_bool_227_926' & 0<=m_1811) & S!=() & 
  S=union(S1_1812,{v_1809}))))))))))))) --> DEL2(a,S,S1),
 (exists(r_1876:exists(v_node_228_1874:exists(m_1877:exists(m_1872:exists(n:exists(n_1837:exists(v_node_228_925':exists(m:exists(v_bool_224_927':exists(v_bool_227_926':exists(x:exists(res:exists(m_1811:exists(S1_1878:exists(v_1875:exists(S1_1812:exists(v_1809:(r_1876=v_node_228_1874 & 
  S1_1873=S1_1878 & S_1838=S1_1812 & v_1809=v_1875 & 1+m_1877=m & 1+
  m_1872=m & -1+n=m_1811 & n_1837=m_1811 & v_node_228_925'=res & 0<=m & (-1+
  m)<=m_1811 & !(v_bool_224_927') & !(v_bool_227_926') & (1+a)<=v_1875 & 
  x!=null & res!=null & 0<=m_1811 & DEL2(a,S_1838,S1_1873) | 
  r_1876=v_node_228_1874 & S1_1873=S1_1878 & S_1838=S1_1812 & 
  v_1809=v_1875 & 1+m_1877=m & 1+m_1872=m & -1+n=m_1811 & n_1837=m_1811 & 
  v_node_228_925'=res & 0<=m & (-1+m)<=m_1811 & !(v_bool_224_927') & 
  !(v_bool_227_926') & (1+v_1875)<=a & x!=null & res!=null & 0<=m_1811 & 
  DEL2(a,S_1838,S1_1873)) & S1=union(S1_1878,{v_1875}) & S=union(S1_1812,
  {v_1809}) & S!=())))))))))))))))))) --> DEL2(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 98::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_22,
                                   m: res::node<m,Anon_22>@M[Orig][]&(
                                   ([FGE(S,m) & (1+v)<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 98::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_2070,
                                 m_2071: res::node<m_2071,Anon_2070>@M[Orig][]&
                                 (
                                 ([res!=null]
                                  [{m_2071}<subset> S  & (1+v)<=m_2071][
                                  0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_22:exists(r_1999:exists(v_node_415_705':exists(m_2000:exists(v:exists(v_bool_411_711':exists(x:exists(v_bool_414_710':exists(n:exists(S1_2001:exists(v_1998:(res=x & 
  Anon_22=r_1999 & m=v_1998 & v_node_415_705'=x & 1+m_2000=n & n<=-1 & (1+
  v)<=v_1998 & v_bool_411_711'<=0 & x!=null & 1<=v_bool_414_710' | res=x & 
  Anon_22=r_1999 & m=v_1998 & v_node_415_705'=x & 1+m_2000=n & (1+
  v)<=v_1998 & v_bool_411_711'<=0 & x!=null & 1<=v_bool_414_710' & 1<=n) & 
  S!=() & S=union(S1_2001,{v_1998})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2001:exists(v_1998:v_1998<=v & S1_2001=S_2024 & 
  m_2052=m & (1+v)<=m & FGE(S_2024,m_2052) & S=union(S1_2001,{v_1998}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S1,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(flted_142_122,flted_142_123,S1,
                                S2: x'::ll2<flted_142_123,S1>@M[Orig][LHSCase]@ rem br[{409}] * 
                                res::ll2<flted_142_122,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (
                                ([1=flted_142_123][1+flted_142_122=n]
                                 [S1!=() & GN(S,S1,S2)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              EXISTS(flted_142_2141,flted_142_2142,S1_2143,
                              S2_2144: x'::ll2<flted_142_2142,S1_2143>@M[Orig][LHSCase]@ rem br[{409}] * 
                              res::ll2<flted_142_2141,S2_2144>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([null!=x'][S1_2143!=()]
                               [1+flted_142_2141=n & 0<=n][1=flted_142_2142]
                               [S2_2144<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_124':exists(res:exists(r_2096:exists(v_node_146_1056':exists(n:exists(flted_142_123:exists(m_2110:exists(r_2109:exists(x:exists(flted_142_122:exists(next_145_1055':exists(x':exists(m_2097:exists(S1_2111:exists(v_2108:exists(S1_2098:exists(v_2095:S1_2111= & 
  (tmp_124'=v_node_146_1056' & res=v_node_146_1056' & 
  r_2096=v_node_146_1056' & -1+n=m_2097 & flted_142_123=1 & m_2110=0 & 
  v_2108=v_2095 & S1_2098=S2 & r_2109=next_145_1055' & x=x' & 
  flted_142_122=m_2097 & next_145_1055'=null & m_2097<=-2 & x'!=null | 
  tmp_124'=v_node_146_1056' & res=v_node_146_1056' & 
  r_2096=v_node_146_1056' & -1+n=m_2097 & flted_142_123=1 & m_2110=0 & 
  v_2108=v_2095 & S1_2098=S2 & r_2109=next_145_1055' & x=x' & 
  flted_142_122=m_2097 & next_145_1055'=null & x'!=null & 0<=m_2097) & 
  S!=() & S1=union(S1_2111,{v_2108}) & S=union(S1_2098,
  {v_2095}))))))))))))))))))) --> GN(S,S1,S2)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                    ([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(flted_182_115,
                                S2: res::ll2<flted_182_115,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([2+flted_182_115=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              EXISTS(flted_182_2214,
                              S2_2215: res::ll2<flted_182_2214,S2_2215>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([2+flted_182_2214=n & 0<=n]
                               [S2_2215<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2194:exists(S1_2197:exists(S1_2166:exists(v_2163:S1_2166=union(S1_2197,
  {v_2194}) & S1_2166!=() & S2=S1_2197 & S!=() & S=union(S1_2166,
  {v_2163})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                    ([0!=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::
                                EXISTS(flted_192_112,
                                S1: x::ll2<flted_192_112,S1>@M[Orig][LHSCase]@ rem br[{409}]&
                                (
                                ([-1+flted_192_112=n][S1!=() & INS(S,S1,a)]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::
                              EXISTS(flted_192_2326,
                              S1_2327: x::ll2<flted_192_2326,S1_2327>@M[Orig][LHSCase]@ rem br[{409}]&
                              (
                              ([S1_2327!=() & S1_2327=union(S,{a})][null!=x]
                               [-1+flted_192_2326=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2284:exists(v_2281:exists(S1_2277:exists(v_2274:exists(S1_2239:exists(v_2236:S1_2284= & 
  S1_2277=union(S1_2284,{v_2281}) & S1_2239= & v_2236=v_2274 & v_2281=a & 
  S1=union(S1_2277,{v_2274}) & S=union(S1_2239,{v_2236}) & 
  S!=()))))))) --> INS(S,S1,a),
 (exists(S1_2303:exists(v_2300:exists(S1_2239:exists(v_2236:S1_2239!=() & 
  S1_2299!=() & v_2300=v_2236 & S1_2239=S_2259 & S1_2299=S1_2303 & 
  INS(S_2259,S1_2299,a) & S!=() & S1=union(S1_2303,{v_2300}) & 
  S=union(S1_2239,{v_2236})))))) --> INS(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CPY(S,S2)
!!! POST:  S=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::
                                EXISTS(n_93,S_94,n_95,
                                S2: x::ll2<n_93,S_94>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                                res::ll2<n_95,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([S=S_94 & CPY(S,S2)][n=n_95 & n=n_93]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::
                              EXISTS(n_2455,S_2456,n_2457,
                              S2_2458: x::ll2<n_2455,S_2456>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                              res::ll2<n_2457,S2_2458>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S=S_2456 & S=S2_2458]
                               [n=n_2455 & n=n_2457 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S_94=S & S_94=)) --> CPY(S,S2),
 (exists(S_94:exists(S1_2386:exists(v_2383:exists(S1_2399:exists(v_2396:exists(S1_2354:exists(v_2351:S_94=union(S1_2386,
  {v_2383}) & S1_2386=S1_2354 & S_2358=S1_2354 & v_2396=v_2383 & 
  v_2351=v_2383 & S2_2378=S1_2399 & CPY(S_2358,S2_2378) & S2=union(S1_2399,
  {v_2396}) & S=union(S1_2354,{v_2351}) & S!=())))))))) --> CPY(S,S2),
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 90::
                                EXISTS(m,
                                S2: res::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([m<=n][FIL(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 90::
                              EXISTS(m_2617,
                              S2_2618: res::ll2<m_2617,S2_2618>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([m_2617<=n & 0<=n][S2_2618<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2485:exists(v_2482:Anon_11=v & 
  v_2482=v & S1_2485=S_2507 & S2_2569=S2 & FIL(S_2507,S2_2569) & S!=() & 
  S=union(S1_2485,{v_2482})))))) --> FIL(S,S2),
 (exists(r_2577:exists(tmp_90':exists(x:exists(res:exists(m_2578:exists(m_2554:exists(n_2528:exists(n:exists(m:exists(v_bool_385_732':exists(v:exists(v_node_398_734':exists(v_bool_384_733':exists(m_2484:exists(S1_2485:exists(v_2482:exists(S1_2579:exists(v_2576:(r_2577=tmp_90' & 
  x=v_node_398_734' & res=v_node_398_734' & S2_2555=S1_2579 & 
  S1_2485=S_2529 & v_2482=v_2576 & 1+m_2578=m & 1+m_2554=m & n_2528=m_2484 & 
  -1+n=m_2484 & 0<=m & (-1+m)<=m_2484 & !(v_bool_385_732') & (1+v)<=v_2576 & 
  v_node_398_734'!=null & v_bool_384_733' & FIL(S_2529,S2_2555) & 
  0<=m_2484 | r_2577=tmp_90' & x=v_node_398_734' & res=v_node_398_734' & 
  S2_2555=S1_2579 & S1_2485=S_2529 & v_2482=v_2576 & 1+m_2578=m & 1+
  m_2554=m & n_2528=m_2484 & -1+n=m_2484 & 0<=m & (-1+m)<=m_2484 & 
  !(v_bool_385_732') & (1+v_2576)<=v & v_node_398_734'!=null & 
  v_bool_384_733' & FIL(S_2529,S2_2555) & 0<=m_2484) & S=union(S1_2485,
  {v_2482}) & S2=union(S1_2579,{v_2576}) & 
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 83::
                                EXISTS(m,
                                S2: res::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([m<=n][RMV2(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 83::
                              EXISTS(m_2980,
                              S2_2981: res::ll2<m_2980,S2_2981>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([m_2980<=n & 0<=n][S2_2981<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(v:exists(Anon_11:exists(Anon_12:exists(r_2860:exists(v_node_373_757':exists(res:exists(m:exists(tmp_91':exists(v_bool_362_755':exists(x:exists(v_bool_361_756':exists(m_2861:exists(S1_2862:exists(v_2859:(-1+
  n=m_2861 & S1_2862=S2 & v_2859=Anon_11 & v=Anon_11 & Anon_12=res & 
  r_2860=res & v_node_373_757'=res & m=m_2861 & m_2861<=-2 & tmp_91'=null & 
  1<=v_bool_362_755' & x!=null & 1<=v_bool_361_756' | -1+n=m_2861 & 
  S1_2862=S2 & v_2859=Anon_11 & v=Anon_11 & Anon_12=res & r_2860=res & 
  v_node_373_757'=res & m=m_2861 & tmp_91'=null & 1<=v_bool_362_755' & 
  x!=null & 1<=v_bool_361_756' & 0<=m_2861) & S!=() & S=union(S1_2862,
  {v_2859}))))))))))))))))) --> RMV2(S,S2),
 (exists(r_2926:exists(tmp_91':exists(x:exists(res:exists(m_2927:exists(m_2913:exists(n_2887:exists(n:exists(m:exists(v_bool_362_755':exists(v:exists(v_node_373_757':exists(v_bool_361_756':exists(m_2861:exists(S1_2862:exists(v_2859:exists(S1_2928:exists(v_2925:(r_2926=tmp_91' & 
  x=v_node_373_757' & res=v_node_373_757' & S2_2914=S1_2928 & 
  S1_2862=S_2888 & v_2859=v_2925 & 1+m_2927=m & 1+m_2913=m & n_2887=m_2861 & 
  -1+n=m_2861 & 0<=m & (-1+m)<=m_2861 & !(v_bool_362_755') & (1+v)<=v_2925 & 
  v_node_373_757'!=null & v_bool_361_756' & RMV2(S_2888,S2_2914) & 
  0<=m_2861 | r_2926=tmp_91' & x=v_node_373_757' & res=v_node_373_757' & 
  S2_2914=S1_2928 & S1_2862=S_2888 & v_2859=v_2925 & 1+m_2927=m & 1+
  m_2913=m & n_2887=m_2861 & -1+n=m_2861 & 0<=m & (-1+m)<=m_2861 & 
  !(v_bool_362_755') & (1+v_2925)<=v & v_node_373_757'!=null & 
  v_bool_361_756' & RMV2(S_2888,S2_2914) & 0<=m_2861) & S=union(S1_2862,
  {v_2859}) & S2=union(S1_2928,{v_2925}) & 
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
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 73::
                                EXISTS(n_97,
                                S2: x::ll2<n_97,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([TRAV(S1,S2)][n=n_97]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 73::
                              EXISTS(n_3065,
                              S2_3066: x::ll2<n_3065,S2_3066>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([S1=S2_3066][n=n_3065 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_3032:exists(v_3029:exists(S1_3009:exists(v_3006:v_3029=v_3006 & 
  S1_3009=S1_3013 & S2_3028=S1_3032 & TRAV(S1_3013,S2_3028) & 
  S2=union(S1_3032,{v_3029}) & S1!=() & S1=union(S1_3009,
  {v_3006})))))) --> TRAV(S1,S2),
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
                    S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{409}]&(
                    ([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(flted_106_127,
                                S2: x'::ll2<flted_106_127,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([1+flted_106_127=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{409}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              EXISTS(flted_106_3118,
                              S2_3119: x'::ll2<flted_106_3118,S2_3119>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([1+flted_106_3118=m & 0<=m]
                               [S2_3119<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_128':exists(r_3088:exists(x':exists(x:exists(flted_106_127:exists(next_110_1102':exists(v_node_111_1103':exists(m_3089:exists(S1_3090:exists(v_3087:(-1+
  m=m_3089 & S1_3090=S2 & res=v_node_111_1103' & tmp_128'=v_node_111_1103' & 
  r_3088=x' & x=v_node_111_1103' & flted_106_127=m_3089 & m_3089<=-2 & 
  next_110_1102'=null & v_node_111_1103'!=null | -1+m=m_3089 & S1_3090=S2 & 
  res=v_node_111_1103' & tmp_128'=v_node_111_1103' & r_3088=x' & 
  x=v_node_111_1103' & flted_106_127=m_3089 & next_110_1102'=null & 
  v_node_111_1103'!=null & 0<=m_3089) & S1=union(S1_3090,{v_3087}) & 
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(flted_95_130,
                                S1: x'::ll2<flted_95_130,S1>@M[Orig][LHSCase]@ rem br[{409}]&
                                (
                                ([-1+flted_95_130=n][S1!=() & PUF(S1,S,v)]
                                 [null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(flted_95_3135,
                              S1_3136: x'::ll2<flted_95_3135,S1_3136>@M[Orig][LHSCase]@ rem br[{409}]&
                              (
                              ([S1_3136!=() & S1_3136=union(S,{v})][null!=x']
                               [-1+flted_95_3135=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3125:exists(v_3122:v=v_3122 & S1_3125=S & S1=union(S1_3125,
  {v_3122})))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(n_125,
                                S2: x::ll2<n_125,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([n=n_125]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(n_3141,
                              S2_3142: x::ll2<n_3141,S2_3142>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([n=n_3141 & 0<=n][S1=S2_3142][res=x]))&
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
                    S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                    ys::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 60::ref [xs;ys]
                                EXISTS(flted_267_106,
                                S: ys'::ll2<flted_267_106,S>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (
                                ([flted_267_106=m+n][null=xs'][REV(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                  ys::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 60::ref [xs;ys]
                              EXISTS(flted_267_3239,
                              S_3240: ys'::ll2<flted_267_3239,S_3240>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S_3240=union(S1,S2)][xs'=null]
                               [flted_267_3239=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3192:exists(S1_3195:exists(S1_3173:exists(v_3170:S2_3186=union(S1_3195,
  {v_3192}) & S_3222!=() & v_3192=v_3170 & S1_3173=S1_3184 & S_3222=S & 
  S2=S1_3195 & REV(S_3222,S1_3184,S2_3186) & S1=union(S1_3173,{v_3170}) & 
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
                    t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                    y::ll2<j,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([x!=null][0<=Anon_16][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(k,
                                S2: x::ll2<k,S2>@M[Orig][LHSCase]@ rem br[{409}]&
                                (([-1+k=j][S2!=() & SN(S,S2,v)][null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig][] * 
                  t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                  y::ll2<j,S>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                  ([x!=null][0<=Anon_16]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              EXISTS(k_3257,S2_3258: true&(
                              ([S2_3258!=() & S2_3258=union(S,{v})][null!=x]
                               [-1+k_3257=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3247:exists(v_3244:v=v_3244 & S1_3247=S & S2=union(S1_3247,
  {v_3244})))) --> SN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 101::ref [x]
                                EXISTS(flted_427_87,
                                S: x'::ll2<flted_427_87,S>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([flted_427_87=m+n][SPI(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 101::ref [x]
                              EXISTS(flted_427_3598,
                              S_3599: x'::ll2<flted_427_3598,S_3599>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S_3599=union(S1,S2)]
                               [flted_427_3598=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> SPI(S,S1,S2),
 (exists(v_3545:exists(S1_3548:exists(S1_3541:exists(v_3538:exists(S1_3478:exists(v_3475:exists(S1_3447:exists(v_3444:S1_3541=union(S1_3548,
  {v_3545}) & S2_3489=S1_3478 & S1_3447=S1_3487 & v_3444=v_3538 & 
  v_3475=v_3545 & S_3527=S1_3548 & SPI(S_3527,S1_3487,S2_3489) & S1!=() & 
  S=union(S1_3541,{v_3538}) & S2!=() & S2=union(S1_3478,{v_3475}) & 
  S1=union(S1_3447,{v_3444})))))))))) --> SPI(S,S1,S2),
 (exists(m:exists(x:exists(flted_427_87:exists(v_bool_432_688':exists(y:exists(v_bool_429_689':exists(x':exists(n:(S1=S & 
  m=0 & x=x' & flted_427_87=n & n<=-1 & v_bool_432_688'<=0 & y=null & 
  v_bool_429_689'<=0 & x'!=null | S1=S & m=0 & x=x' & flted_427_87=n & 
  v_bool_432_688'<=0 & y=null & v_bool_429_689'<=0 & x'!=null & 1<=n) & 
  S1!=() & S2=))))))))) --> SPI(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::ref [x]
                                EXISTS(n2,n1,S1,
                                S2: x'::ll2<n1,S1>@M[Orig][LHSCase]@ rem br[{409}] * 
                                res::ll2<n2,S2>@M[Orig][LHSCase]@ rem br[{409}]&
                                (
                                ([a=n1 & 0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][null!=x']
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{409}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 66::ref [x]
                              EXISTS(n2_3829,n1_3830,S1_3831,
                              S2_3832: x'::ll2<n1_3830,S1_3831>@M[Orig][LHSCase]@ rem br[{409}] * 
                              res::ll2<n2_3829,S2_3832>@M[Orig][LHSCase]@ rem br[{409}]&
                              (
                              ([S1_3831!=() & S2_3832!=() & union(S1_3831,
                                 S2_3832)=S]
                               [null!=res][null!=x']
                               [a=n1_3830 & 0!=n1_3830 & 0<=n & n=n1_3830+
                                 n2_3829 & 0!=n2_3829]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3714:exists(v_3711:exists(S1_3634:exists(v_3631:S1_3634!=() & 
  S1_3714= & v_3711=v_3631 & S1_3634=S2 & S1=union(S1_3714,{v_3711}) & 
  S!=() & S=union(S1_3634,{v_3631})))))) --> SPLIT(S,S1,S2),
 (exists(S1_3749:exists(v_3746:exists(S1_3673:exists(v_3670:S1_3673!=() & 
  S2_3743!=() & S1_3742!=() & v_3746=v_3670 & S1_3673=S_3675 & 
  S1_3742=S1_3749 & S2_3743=S2 & SPLIT(S_3675,S1_3742,S2_3743) & 
  S1=union(S1_3749,{v_3746}) & S=union(S1_3673,{v_3670}) & 
  S!=()))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_133,n_134,S3,
                                S4: x'::ll2<m_133,S3>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                                y'::ll2<n_134,S4>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                (([m=m_133][n=n_134]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]@ rem br[{410,409}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(m_3842,S3_3843,n_3844,
                              S4_3845: x'::ll2<m_3842,S3_3843>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                              y'::ll2<n_3844,S4_3845>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([m=m_3842 & 0<=m][n=n_3844 & 0<=n][S1=S4_3845]
                               [S2=S3_3843][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (166,13)  (166,4)  (253,4)  (253,11)  (258,4)  (258,11)  (257,10)  (257,4)  (256,8)  (256,12)  (256,4)  (256,4) )

Total verification time: 4.45 second(s)
	Time spent in main process: 0.83 second(s)
	Time spent in child processes: 3.62 second(s)
