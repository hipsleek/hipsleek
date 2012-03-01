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
                              EXISTS(m_1464,
                              S_1465: x::ll2<m_1464,S_1465>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([union(S1,S2)=S_1465]
                               [m_1464=n1+n2 & 0<=n1 & 0<=n2]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1414:exists(v_1411:exists(S1_1372:exists(v_1369:S1_1372= & 
  v_1369=v_1411 & S1_1414=S2 & S=union(S1_1414,{v_1411}) & S1!=() & 
  S1=union(S1_1372,{v_1369})))))) --> APP(S,S1,S2),
 (exists(S1_1435:exists(v_1432:exists(S1_1372:exists(v_1369:S_1431!=() & 
  S1_1372!=() & S1_1372=S1_1391 & v_1369=v_1432 & S_1431=S1_1435 & 
  S2_1393=S2 & APP(S_1431,S1_1391,S2_1393) & S=union(S1_1435,{v_1432}) & 
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
                                                       EXISTS(S_1487: 
                                                       x'::ll2<n_132,S4>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                                       (
                                                       ([S4=S_1487 & 
                                                          467::forall(x_1479:x_1479 <notin> S_1487
                                                           | x_1479=v) & 
                                                          S_1487!=()]
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
                                                       EXISTS(n_1585,
                                                       S_1586: res::ll2<n_1585,S_1586>@M[Orig][LHSCase]@ rem br[{410,409}]&
                                                       (
                                                       ([n=n_1585 & 1<=n]
                                                        [forall(_x:_x <notin> S_1586
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
!!! NEW RELS:[ (exists(S1_1540:exists(v_1537:S1_1540= & v_1537=v & S=union(S1_1540,
  {v_1537})))) --> CL(S,v),
 (exists(S1_1557:exists(v_1554:S_1552!=() & S1_1557=S_1552 & v=v_1554 & 
  CL(S_1552,v) & S=union(S1_1557,{v_1554})))) --> CL(S,v)]
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
                              EXISTS(m_1808,
                              S1_1809: x::ll2<m_1808,S1_1809>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([S1_1809<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1653:exists(S1_1656:exists(S1_1623:exists(v_1620:exists(S1_1735:exists(v_1732:S1_1623!=() & 
  S1_1623=union(S1_1656,{v_1653}) & S1_1735=S1_1656 & v_1620=v_1732 & 
  S=union(S1_1623,{v_1620}) & S1=union(S1_1735,{v_1732}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1688:exists(m_1689:exists(n_1702:exists(a:exists(m_1765:exists(m_1760:exists(v_int_213_1762:exists(n:exists(v_bool_209_952':exists(x:exists(r_1764:exists(m:exists(S1_1766:exists(v_1763:exists(S1_1690:exists(v_1687:S1_1690!=() & 
  S1_1761!=() & (r_1688=r_1764 & S1_1761=S1_1766 & S1_1690=S_1703 & 
  v_1763=v_1687 & 1+m_1689=n & 1+n_1702=n & -1+a=v_int_213_1762 & m=0 & 
  m_1765=-1 & m_1760=-1 & 1<=v_int_213_1762 & (2+v_int_213_1762)<=n & 
  !(v_bool_209_952') & x!=null & r_1764!=null & DEL(S_1703,S1_1761) | 
  r_1688=r_1764 & S1_1761=S1_1766 & S1_1690=S_1703 & v_1763=v_1687 & 1+
  m_1689=n & 1+n_1702=n & -1+a=v_int_213_1762 & 1+m_1765=m & 1+m_1760=m & 
  1<=v_int_213_1762 & (2+v_int_213_1762)<=n & !(v_bool_209_952') & x!=null & 
  r_1764!=null & DEL(S_1703,S1_1761) & 2<=m) & S!=() & S1=union(S1_1766,
  {v_1763}) & S=union(S1_1690,{v_1687})))))))))))))))))) --> DEL(S,S1)]
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
                              EXISTS(m_1958,
                              S1_1959: res::ll2<m_1958,S1_1959>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([m_1958<=n & 0<=n]
                               [S1_1959=S & a <notin> S  | S1_1959<subset> S
                                  & a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> DEL2(a,S,S1),
 (exists(n:exists(r_1835:exists(res:exists(v_node_227_917':exists(m:exists(v_bool_224_927':exists(x:exists(v_bool_227_926':exists(m_1836:exists(S1_1837:exists(v_1834:(v_1834=a & 
  S1_1837=S1 & -1+n=m_1836 & r_1835=v_node_227_917' & res=v_node_227_917' & 
  m=m_1836 & m_1836<=-2 & v_bool_224_927'<=0 & x!=null & 
  1<=v_bool_227_926' | v_1834=a & S1_1837=S1 & -1+n=m_1836 & 
  r_1835=v_node_227_917' & res=v_node_227_917' & m=m_1836 & 
  v_bool_224_927'<=0 & x!=null & 1<=v_bool_227_926' & 0<=m_1836) & S!=() & 
  S=union(S1_1837,{v_1834}))))))))))))) --> DEL2(a,S,S1),
 (exists(r_1904:exists(v_node_228_1902:exists(m_1905:exists(m_1900:exists(n:exists(n_1862:exists(v_node_228_925':exists(m:exists(v_bool_224_927':exists(v_bool_227_926':exists(x:exists(res:exists(m_1836:exists(S1_1906:exists(v_1903:exists(S1_1837:exists(v_1834:(r_1904=v_node_228_1902 & 
  S1_1901=S1_1906 & S_1863=S1_1837 & v_1834=v_1903 & 1+m_1905=m & 1+
  m_1900=m & -1+n=m_1836 & n_1862=m_1836 & v_node_228_925'=res & 0<=m & (-1+
  m)<=m_1836 & !(v_bool_224_927') & !(v_bool_227_926') & (1+a)<=v_1903 & 
  x!=null & res!=null & 0<=m_1836 & DEL2(a,S_1863,S1_1901) | 
  r_1904=v_node_228_1902 & S1_1901=S1_1906 & S_1863=S1_1837 & 
  v_1834=v_1903 & 1+m_1905=m & 1+m_1900=m & -1+n=m_1836 & n_1862=m_1836 & 
  v_node_228_925'=res & 0<=m & (-1+m)<=m_1836 & !(v_bool_224_927') & 
  !(v_bool_227_926') & (1+v_1903)<=a & x!=null & res!=null & 0<=m_1836 & 
  DEL2(a,S_1863,S1_1901)) & S1=union(S1_1906,{v_1903}) & S=union(S1_1837,
  {v_1834}) & S!=())))))))))))))))))) --> DEL2(a,S,S1)]
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
                              or EXISTS(Anon_2110,
                                 m_2111: res::node<m_2111,Anon_2110>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_2111 & m_2111 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_22:exists(r_2034:exists(v_node_415_705':exists(m_2035:exists(v:exists(v_bool_411_711':exists(x:exists(v_bool_414_710':exists(n:exists(S1_2036:exists(v_2033:(res=x & 
  Anon_22=r_2034 & m=v_2033 & v_node_415_705'=x & 1+m_2035=n & n<=-1 & (1+
  v)<=v_2033 & v_bool_411_711'<=0 & x!=null & 1<=v_bool_414_710' | res=x & 
  Anon_22=r_2034 & m=v_2033 & v_node_415_705'=x & 1+m_2035=n & (1+
  v)<=v_2033 & v_bool_411_711'<=0 & x!=null & 1<=v_bool_414_710' & 1<=n) & 
  S!=() & S=union(S1_2036,{v_2033})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2036:exists(v_2033:v_2033<=v & S1_2036=S_2059 & 
  m_2090=m & (1+v)<=m & FGE(S_2059,m_2090) & S=union(S1_2036,{v_2033}) & 
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
                              EXISTS(flted_142_2184,flted_142_2185,S1_2186,
                              S2_2187: x'::ll2<flted_142_2185,S1_2186>@M[Orig][LHSCase]@ rem br[{409}] * 
                              res::ll2<flted_142_2184,S2_2187>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S1_2186!=() & union(S1_2186,S2_2187)=S]
                               [null!=x'][1+flted_142_2184=n & 0<=n]
                               [1=flted_142_2185]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(tmp_124':exists(res:exists(r_2136:exists(v_node_146_1056':exists(n:exists(flted_142_123:exists(m_2150:exists(r_2149:exists(x:exists(flted_142_122:exists(next_145_1055':exists(x':exists(m_2137:exists(S1_2151:exists(v_2148:exists(S1_2138:exists(v_2135:S1_2151= & 
  (tmp_124'=v_node_146_1056' & res=v_node_146_1056' & 
  r_2136=v_node_146_1056' & -1+n=m_2137 & flted_142_123=1 & m_2150=0 & 
  v_2148=v_2135 & S1_2138=S2 & r_2149=next_145_1055' & x=x' & 
  flted_142_122=m_2137 & next_145_1055'=null & m_2137<=-2 & x'!=null | 
  tmp_124'=v_node_146_1056' & res=v_node_146_1056' & 
  r_2136=v_node_146_1056' & -1+n=m_2137 & flted_142_123=1 & m_2150=0 & 
  v_2148=v_2135 & S1_2138=S2 & r_2149=next_145_1055' & x=x' & 
  flted_142_122=m_2137 & next_145_1055'=null & x'!=null & 0<=m_2137) & 
  S!=() & S1=union(S1_2151,{v_2148}) & S=union(S1_2138,
  {v_2135}))))))))))))))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
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
                              EXISTS(flted_182_2259,
                              S2_2260: res::ll2<flted_182_2259,S2_2260>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([2+flted_182_2259=n & 0<=n]
                               [S2_2260<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2237:exists(S1_2240:exists(S1_2209:exists(v_2206:S1_2209=union(S1_2240,
  {v_2237}) & S1_2209!=() & S2=S1_2240 & S!=() & S=union(S1_2209,
  {v_2206})))))) --> GNN(S,S2)]
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
                              EXISTS(flted_192_2376,
                              S1_2377: x::ll2<flted_192_2376,S1_2377>@M[Orig][LHSCase]@ rem br[{409}]&
                              (
                              ([S1_2377!=() & S1_2377=union(S,{a})][null!=x]
                               [-1+flted_192_2376=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2329:exists(v_2326:exists(S1_2322:exists(v_2319:exists(S1_2284:exists(v_2281:S1_2329= & 
  S1_2322=union(S1_2329,{v_2326}) & S1_2284= & v_2281=v_2319 & v_2326=a & 
  S1=union(S1_2322,{v_2319}) & S=union(S1_2284,{v_2281}) & 
  S!=()))))))) --> INS(S,S1,a),
 (exists(S1_2348:exists(v_2345:exists(S1_2284:exists(v_2281:S1_2284!=() & 
  S1_2344!=() & v_2345=v_2281 & S1_2284=S_2304 & S1_2344=S1_2348 & 
  INS(S_2304,S1_2344,a) & S!=() & S1=union(S1_2348,{v_2345}) & 
  S=union(S1_2284,{v_2281})))))) --> INS(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(S,S2)
!!! POST:  S2=S
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
                              EXISTS(n_2509,S_2510,n_2511,
                              S2_2512: x::ll2<n_2509,S_2510>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                              res::ll2<n_2511,S2_2512>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S=S_2510 & S=S2_2512]
                               [n=n_2509 & n=n_2511 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S_94=S & S_94=)) --> CPY(S,S2),
 (exists(S_94:exists(S1_2436:exists(v_2433:exists(S1_2449:exists(v_2446:exists(S1_2404:exists(v_2401:S_94=union(S1_2436,
  {v_2433}) & S1_2436=S1_2404 & S_2408=S1_2404 & v_2446=v_2433 & 
  v_2401=v_2433 & S2_2428=S1_2449 & CPY(S_2408,S2_2428) & S2=union(S1_2449,
  {v_2446}) & S=union(S1_2404,{v_2401}) & S!=())))))))) --> CPY(S,S2),
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
                              EXISTS(m_2680,
                              S2_2681: res::ll2<m_2680,S2_2681>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([m_2680<=n & 0<=n][S2_2681<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(Anon_11:exists(v:exists(S1_2539:exists(v_2536:Anon_11=v & 
  v_2536=v & S1_2539=S_2561 & S2_2623=S2 & FIL(S_2561,S2_2623) & S!=() & 
  S=union(S1_2539,{v_2536})))))) --> FIL(S,S2),
 (exists(r_2632:exists(tmp_90':exists(x:exists(res:exists(m_2633:exists(m_2608:exists(n_2582:exists(n:exists(m:exists(v_bool_385_732':exists(v:exists(v_node_398_734':exists(v_bool_384_733':exists(m_2538:exists(S1_2539:exists(v_2536:exists(S1_2634:exists(v_2631:(r_2632=tmp_90' & 
  x=v_node_398_734' & res=v_node_398_734' & S2_2609=S1_2634 & 
  S1_2539=S_2583 & v_2536=v_2631 & 1+m_2633=m & 1+m_2608=m & n_2582=m_2538 & 
  -1+n=m_2538 & 0<=m & (-1+m)<=m_2538 & !(v_bool_385_732') & (1+v)<=v_2631 & 
  v_node_398_734'!=null & v_bool_384_733' & FIL(S_2583,S2_2609) & 
  0<=m_2538 | r_2632=tmp_90' & x=v_node_398_734' & res=v_node_398_734' & 
  S2_2609=S1_2634 & S1_2539=S_2583 & v_2536=v_2631 & 1+m_2633=m & 1+
  m_2608=m & n_2582=m_2538 & -1+n=m_2538 & 0<=m & (-1+m)<=m_2538 & 
  !(v_bool_385_732') & (1+v_2631)<=v & v_node_398_734'!=null & 
  v_bool_384_733' & FIL(S_2583,S2_2609) & 0<=m_2538) & S=union(S1_2539,
  {v_2536}) & S2=union(S1_2634,{v_2631}) & 
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
                              EXISTS(m_3054,
                              S2_3055: res::ll2<m_3054,S2_3055>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([m_3054<=n & 0<=n][S2_3055<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(n:exists(v:exists(Anon_11:exists(Anon_12:exists(r_2923:exists(v_node_373_757':exists(res:exists(m:exists(tmp_91':exists(v_bool_362_755':exists(x:exists(v_bool_361_756':exists(m_2924:exists(S1_2925:exists(v_2922:(-1+
  n=m_2924 & S1_2925=S2 & v_2922=Anon_11 & v=Anon_11 & Anon_12=res & 
  r_2923=res & v_node_373_757'=res & m=m_2924 & m_2924<=-2 & tmp_91'=null & 
  1<=v_bool_362_755' & x!=null & 1<=v_bool_361_756' | -1+n=m_2924 & 
  S1_2925=S2 & v_2922=Anon_11 & v=Anon_11 & Anon_12=res & r_2923=res & 
  v_node_373_757'=res & m=m_2924 & tmp_91'=null & 1<=v_bool_362_755' & 
  x!=null & 1<=v_bool_361_756' & 0<=m_2924) & S!=() & S=union(S1_2925,
  {v_2922}))))))))))))))))) --> RMV2(S,S2),
 (exists(r_2992:exists(tmp_91':exists(x:exists(res:exists(m_2993:exists(m_2976:exists(n_2950:exists(n:exists(m:exists(v_bool_362_755':exists(v:exists(v_node_373_757':exists(v_bool_361_756':exists(m_2924:exists(S1_2925:exists(v_2922:exists(S1_2994:exists(v_2991:(r_2992=tmp_91' & 
  x=v_node_373_757' & res=v_node_373_757' & S2_2977=S1_2994 & 
  S1_2925=S_2951 & v_2922=v_2991 & 1+m_2993=m & 1+m_2976=m & n_2950=m_2924 & 
  -1+n=m_2924 & 0<=m & (-1+m)<=m_2924 & !(v_bool_362_755') & (1+v)<=v_2991 & 
  v_node_373_757'!=null & v_bool_361_756' & RMV2(S_2951,S2_2977) & 
  0<=m_2924 | r_2992=tmp_91' & x=v_node_373_757' & res=v_node_373_757' & 
  S2_2977=S1_2994 & S1_2925=S_2951 & v_2922=v_2991 & 1+m_2993=m & 1+
  m_2976=m & n_2950=m_2924 & -1+n=m_2924 & 0<=m & (-1+m)<=m_2924 & 
  !(v_bool_362_755') & (1+v_2991)<=v & v_node_373_757'!=null & 
  v_bool_361_756' & RMV2(S_2951,S2_2977) & 0<=m_2924) & S=union(S1_2925,
  {v_2922}) & S2=union(S1_2994,{v_2991}) & 
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
                              EXISTS(n_3142,
                              S2_3143: x::ll2<n_3142,S2_3143>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([S1=S2_3143][n=n_3142 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_3106:exists(v_3103:exists(S1_3083:exists(v_3080:v_3103=v_3080 & 
  S1_3083=S1_3087 & S2_3102=S1_3106 & TRAV(S1_3087,S2_3102) & 
  S2=union(S1_3106,{v_3103}) & S1!=() & S1=union(S1_3083,
  {v_3080})))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_106_3198,
                              S2_3199: x'::ll2<flted_106_3198,S2_3199>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([1+flted_106_3198=m & 0<=m]
                               [S2_3199<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_128':exists(r_3165:exists(x':exists(x:exists(flted_106_127:exists(next_110_1102':exists(v_node_111_1103':exists(m_3166:exists(S1_3167:exists(v_3164:(-1+
  m=m_3166 & S1_3167=S2 & res=v_node_111_1103' & tmp_128'=v_node_111_1103' & 
  r_3165=x' & x=v_node_111_1103' & flted_106_127=m_3166 & m_3166<=-2 & 
  next_110_1102'=null & v_node_111_1103'!=null | -1+m=m_3166 & S1_3167=S2 & 
  res=v_node_111_1103' & tmp_128'=v_node_111_1103' & r_3165=x' & 
  x=v_node_111_1103' & flted_106_127=m_3166 & next_110_1102'=null & 
  v_node_111_1103'!=null & 0<=m_3166) & S1=union(S1_3167,{v_3164}) & 
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
                              EXISTS(flted_95_3217,
                              S1_3218: x'::ll2<flted_95_3217,S1_3218>@M[Orig][LHSCase]@ rem br[{409}]&
                              (
                              ([S1_3218!=() & S1_3218=union(S,{v})][null!=x']
                               [-1+flted_95_3217=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3205:exists(v_3202:v=v_3202 & S1_3205=S & S1=union(S1_3205,
  {v_3202})))) --> PUF(S1,S,v)]
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
                              EXISTS(n_3223,
                              S2_3224: x::ll2<n_3223,S2_3224>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (([n=n_3223 & 0<=n][S1=S2_3224][res=x]))&
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
                              EXISTS(flted_267_3327,
                              S_3328: ys'::ll2<flted_267_3327,S_3328>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S_3328=union(S1,S2)][xs'=null]
                               [flted_267_3327=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3274:exists(S1_3277:exists(S1_3255:exists(v_3252:S2_3268=union(S1_3277,
  {v_3274}) & S_3304!=() & v_3274=v_3252 & S1_3255=S1_3266 & S_3304=S & 
  S2=S1_3277 & REV(S_3304,S1_3266,S2_3268) & S1=union(S1_3255,{v_3252}) & 
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
                              EXISTS(k_3347,S2_3348: true&(
                              ([S2_3348!=() & S2_3348=union(S,{v})][null!=x]
                               [-1+k_3347=j & 0<=j][0<=Anon_16]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3335:exists(v_3332:v=v_3332 & S1_3335=S & S2=union(S1_3335,
  {v_3332})))) --> SN(S,S2,v)]
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
                              EXISTS(flted_427_3697,
                              S_3698: x'::ll2<flted_427_3697,S_3698>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([S_3698=union(S1,S2)]
                               [flted_427_3697=m+n & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> SPI(S,S1,S2),
 (exists(v_3635:exists(S1_3638:exists(S1_3631:exists(v_3628:exists(S1_3568:exists(v_3565:exists(S1_3537:exists(v_3534:S1_3631=union(S1_3638,
  {v_3635}) & S2_3579=S1_3568 & S1_3537=S1_3577 & v_3534=v_3628 & 
  v_3565=v_3635 & S_3617=S1_3638 & SPI(S_3617,S1_3577,S2_3579) & S1!=() & 
  S=union(S1_3631,{v_3628}) & S2!=() & S2=union(S1_3568,{v_3565}) & 
  S1=union(S1_3537,{v_3534})))))))))) --> SPI(S,S1,S2),
 (exists(m:exists(x:exists(flted_427_87:exists(v_bool_432_688':exists(y:exists(v_bool_429_689':exists(x':exists(n:(S1=S & 
  m=0 & x=x' & flted_427_87=n & n<=-1 & v_bool_432_688'<=0 & y=null & 
  v_bool_429_689'<=0 & x'!=null | S1=S & m=0 & x=x' & flted_427_87=n & 
  v_bool_432_688'<=0 & y=null & v_bool_429_689'<=0 & x'!=null & 1<=n) & 
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
                              EXISTS(n2_3936,n1_3937,S1_3938,
                              S2_3939: x'::ll2<n1_3937,S1_3938>@M[Orig][LHSCase]@ rem br[{409}] * 
                              res::ll2<n2_3936,S2_3939>@M[Orig][LHSCase]@ rem br[{409}]&
                              (
                              ([S1_3938!=() & S2_3939!=() & union(S1_3938,
                                 S2_3939)=S]
                               [null!=res][null!=x']
                               [a=n1_3937 & 0!=n1_3937 & 0<=n & n=n1_3937+
                                 n2_3936 & 0!=n2_3936]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3813:exists(v_3810:exists(S1_3733:exists(v_3730:S1_3733!=() & 
  S1_3813= & v_3810=v_3730 & S1_3733=S2 & S1=union(S1_3813,{v_3810}) & 
  S!=() & S=union(S1_3733,{v_3730})))))) --> SPLIT(S,S1,S2),
 (exists(S1_3849:exists(v_3846:exists(S1_3772:exists(v_3769:S1_3772!=() & 
  S2_3843!=() & S1_3842!=() & v_3846=v_3769 & S1_3772=S_3774 & 
  S1_3842=S1_3849 & S2_3843=S2 & SPLIT(S_3774,S1_3842,S2_3843) & 
  S1=union(S1_3849,{v_3846}) & S=union(S1_3772,{v_3769}) & 
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
                              EXISTS(m_3949,S3_3950,n_3951,
                              S4_3952: x'::ll2<m_3949,S3_3950>@M[Orig][LHSCase]@ rem br[{410,409}] * 
                              y'::ll2<n_3951,S4_3952>@M[Orig][LHSCase]@ rem br[{410,409}]&
                              (
                              ([m=m_3949 & 0<=m][n=n_3951 & 0<=n][S1=S4_3952]
                               [S2=S3_3950][y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (166,13)  (166,4)  (253,4)  (253,11)  (258,4)  (258,11)  (257,10)  (257,4)  (256,8)  (256,12)  (256,4)  (256,4) )

Total verification time: 3.97 second(s)
	Time spent in main process: 0.52 second(s)
	Time spent in child processes: 3.45 second(s)
