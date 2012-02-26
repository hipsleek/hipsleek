/usr/local/bin/mona

Processing file "ll_msb.ss"
Parsing ll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure append$node~node... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[n1; S1; n2; 
                    S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase] * 
                    y::ll2<n2,S2>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(m,S: x::ll2<m,S>@M[Orig][LHSCase]&
                                m=n2+n1 & APP(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x::ll2<n1,S1>@M[Orig][LHSCase] * 
                  y::ll2<n2,S2>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              EXISTS(m_1508,
                              S_1509: x::ll2<m_1508,S_1509>@M[Orig][LHSCase]&
                              m_1508=n2+n1 & union(S1,S2)=S_1509 & 0<=n1 & 
                              0<=n2&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1427:exists(v_1425:exists(S1_1393:exists(v_1295:exists(v_1390:exists(S1_1298:(S2= | 
  S2=union(S1_1427,{v_1425})) & S=union(S1_1393,{v_1390}) & S1=union(S1_1298,
  {v_1295}) & S2=S1_1393 & v_1295=v_1390 & S1_1298=))))))) --> APP(S,S1,S2),
 (exists(S1_1487:exists(v_1485:exists(S1_1298:exists(v_1295:exists(S1_1455:exists(v_1452:S_1451=union(S1_1487,
  {v_1485}) & S_1451=S1_1455 & v_1295=v_1452 & S1_1298=S1_1337 & 
  S2=S2_1339 & APP(S_1451,S1_1337,S2_1339) & S1=union(S1_1298,{v_1295}) & 
  S=union(S1_1455,{v_1452})))))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
!!! REL :  CL(S,v)
!!! POST:  forall(_x:_x <notin> S  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&0<=n&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 48::
                                                         true&res=null&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 49::
                                                         EXISTS(n_108,
                                                         S: res::ll2<n_108,S>@M[Orig][LHSCase]&
                                                         CL(S,v) & n_108=n&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 50::
                                                         true&true&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&0<=n&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 48::
                                                       true&res=null & n=0&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 49::
                                                       EXISTS(n_1622,
                                                       S_1623: res::ll2<n_1622,S_1623>@M[Orig][LHSCase]&
                                                       n_1622=n & 
                                                       forall(_x:_x <notin> S_1623
                                                        | _x=v) & 0<n&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 50::
                                                       true&n<0&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_1565:exists(v_1562:S1_1565= & S1_1565= & v=v_1562 & 
  S=union(S1_1565,{v_1562})))) --> CL(S,v),
 (exists(S1_1612:exists(v_1610:exists(S1_1579:exists(v_1576:S_1574=union(S1_1612,
  {v_1610}) & S_1574=S1_1579 & v=v_1576 & CL(S_1574,v) & S=union(S1_1579,
  {v_1576})))))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_131,
                                S4: x'::ll2<n_131,S4>@M[Orig][LHSCase]&
                                n_131=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S3](ex)x::ll2<m,S3>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              x::ll2<m,S3>@M[Orig][LHSCase] * 
                              x'::ll2<n_131,S4>@M[Orig][LHSCase]&n_131=0 & 
                              n=0 & x'=null & S4= & 0<=m&
                              {FLOW,(20,21)=__norm}
                              or x::ll2<m,S3>@M[Orig][LHSCase] * 
                                 x'::ll2<n_131,S4>@M[Orig][LHSCase]&
                                 S_1670_1706=S4 & n=n_131 & 1<=n_131 & 
                                 534::forall(_x:_x <notin> S_1670_1706  | 
                                 _x=v) & 0<=m&{FLOW,(20,21)=__norm}
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(m,S1: x::ll2<m,S1>@M[Orig][LHSCase]&
                                DEL(S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(m_1953,
                              S1_1954: x::ll2<m_1953,S1_1954>@M[Orig][LHSCase]&
                              S1_1954<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1891:exists(v_1889:exists(v_1742:exists(v_1851:exists(S1_1854:exists(S1_1745:exists(S1_1775:exists(v_1772:(S1_1775= | 
  S1_1775=union(S1_1891,{v_1889})) & S1=union(S1_1854,{v_1851}) & 
  S=union(S1_1745,{v_1742}) & v_1742=v_1851 & S1_1775=S1_1854 & 
  S1_1745=union(S1_1775,{v_1772})))))))))) --> DEL(S,S1),
 (exists(S1_1932:exists(v_1930:exists(S1_1803:exists(v_1800:exists(v_1903:exists(S1_1906:(S1_1901= | 
  S1_1901=union(S1_1932,{v_1930})) & S1=union(S1_1906,{v_1903}) & 
  S=union(S1_1803,{v_1800}) & DEL(S_1816,S1_1901) & S1_1803=S_1816 & 
  v_1800=v_1903 & S1_1901=S1_1906))))))) --> DEL(S,S1)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(m,S1: res::ll2<m,S1>@M[Orig][LHSCase]&
                                m<=n & DEL2(a,S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&(a <notin> S  | a <in> S ) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(m_2194,
                              S1_2195: res::ll2<m_2194,S1_2195>@M[Orig][LHSCase]&
                              m_2194<=n & (S1_2195=S & a <notin> S  | 
                              S1_2195<subset> S  & a <in> S ) & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S= & S1=S) --> DEL2(a,S,S1),
 (S1=S & S= & S1=) --> DEL2(a,S,S1),
 (exists(S1_2106:exists(v_2104:exists(S1_1991:exists(v_1988:(S1_1991= | 
  S1_1991=union(S1_2106,{v_2104})) & S=union(S1_1991,{v_1988}) & 
  S1_1991=S1 & a=v_1988))))) --> DEL2(a,S,S1),
 (exists(m_1990:exists(n_2028:exists(v_node_224_909':exists(v_node_224_2116:exists(m_2114:exists(m:exists(m_2119:exists(m_2151:exists(n:exists(v_bool_220_911':exists(v_bool_223_910':exists(x:exists(r_2118:exists(res:exists(S1_2152:exists(v_2150:exists(S1_2120:exists(v_2117:exists(S1_1991:exists(v_1988:(S1_2115= & 
  (S1_1991=S_2029 & 1+m_1990=n & 1+n_2028=n & v_node_224_909'=res & 
  v_1988=v_2117 & v_node_224_2116=r_2118 & m_2114=0 & S1_2115=S1_2120 & 
  m=1 & m_2119=0 & !(v_bool_220_911') & (1+a)<=v_2117 & !(v_bool_223_910') & 
  r_2118=null & x!=null & res!=null & 1<=n & DEL2(a,S_2029,S1_2115) | 
  S1_1991=S_2029 & 1+m_1990=n & 1+n_2028=n & v_node_224_909'=res & 
  v_1988=v_2117 & v_node_224_2116=r_2118 & m_2114=0 & S1_2115=S1_2120 & 
  m=1 & m_2119=0 & !(v_bool_220_911') & !(v_bool_223_910') & r_2118=null & 
  (1+v_2117)<=a & x!=null & res!=null & 1<=n & DEL2(a,S_2029,S1_2115)) | 
  (S1_1991=S_2029 & 1+m_1990=n & 1+n_2028=n & v_node_224_909'=res & 
  v_1988=v_2117 & v_node_224_2116=r_2118 & -1+m_2114=m_2151 & 
  S1_2115=S1_2120 & -2+m=m_2151 & -1+m_2119=m_2151 & 0<=m_2151 & (2+
  m_2151)<=n & !(v_bool_220_911') & (1+a)<=v_2117 & !(v_bool_223_910') & 
  x!=null & r_2118!=null & res!=null & DEL2(a,S_2029,S1_2115) | 
  S1_1991=S_2029 & 1+m_1990=n & 1+n_2028=n & v_node_224_909'=res & 
  v_1988=v_2117 & v_node_224_2116=r_2118 & -1+m_2114=m_2151 & 
  S1_2115=S1_2120 & -2+m=m_2151 & -1+m_2119=m_2151 & 0<=m_2151 & (2+
  m_2151)<=n & !(v_bool_220_911') & !(v_bool_223_910') & (1+v_2117)<=a & 
  x!=null & r_2118!=null & res!=null & DEL2(a,S_2029,S1_2115)) & 
  S1_2115=union(S1_2152,{v_2150})) & S1=union(S1_2120,{v_2117}) & 
  S=union(S1_1991,{v_1988})))))))))))))))))))))) --> DEL2(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 93::
                                
                                true&res=null&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_22,
                                   m: res::node<m,Anon_22>@M[Orig]&v<m & 
                                   FGE(S,m)&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 93::
                              
                              true&res=null & 0<=n&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_2435,
                                 m_2436: res::node<m_2436,Anon_2435>@M[Orig]&
                                 v<m_2436 & {m_2436}<subset> S  & 0<=n&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(S1_2415:exists(v_2413:exists(S1_2326:exists(v:exists(v_2323:(S1_2326= | 
  S1_2326=union(S1_2415,{v_2413})) & S=union(S1_2326,{v_2323}) & (1+v)<=m & 
  v_2323=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2326:exists(v_2323:v_2323<=v & S1_2326=S_2373 & 
  m_2425=m & (1+v)<=m & FGE(S_2373,m_2425) & S=union(S1_2326,
  {v_2323}))))) --> FGE(S,m)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::ref [x]
                                EXISTS(flted_138_121,flted_138_122,S1,
                                S2: x'::ll2<flted_138_122,S1>@M[Orig][LHSCase] * 
                                res::ll2<flted_138_121,S2>@M[Orig][LHSCase]&
                                flted_138_122=1 & flted_138_121+1=n & 
                                GN(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 27::ref [x]
                              EXISTS(flted_138_2520,flted_138_2521,S1_2522,
                              S2_2523: x'::ll2<flted_138_2521,S1_2522>@M[Orig][LHSCase] * 
                              res::ll2<flted_138_2520,S2_2523>@M[Orig][LHSCase]&
                              flted_138_2521=1 & flted_138_2520+1=n & 
                              union(S1_2522,S2_2523)=S & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2511:exists(v_2509:exists(S1_2469:exists(v_2466:exists(v_2477:exists(S1_2480:(S1_2469= | 
  S1_2469=union(S1_2511,{v_2509})) & S1=union(S1_2480,{v_2477}) & 
  S=union(S1_2469,{v_2466}) & S1_2469=S2 & v_2466=v_2477 & S1_2480= & 
  S1_2480=))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&1<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(flted_178_114,
                                S2: res::ll2<flted_178_114,S2>@M[Orig][LHSCase]&
                                flted_178_114+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  2<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              EXISTS(flted_178_2619,
                              S2_2620: res::ll2<flted_178_2619,S2_2620>@M[Orig][LHSCase]&
                              flted_178_2619+2=n & S2_2620<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2606:exists(v_2604:exists(v_2544:exists(S1_2547:exists(S1_2577:exists(v_2574:(S1_2577= | 
  S1_2577=union(S1_2606,{v_2604})) & S=union(S1_2547,{v_2544}) & 
  S1_2577=S2 & S1_2547=union(S1_2577,{v_2574})))))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_188_111,
                                S1: x::ll2<flted_188_111,S1>@M[Orig][LHSCase]&
                                flted_188_111=1+n & INS(S,S1,a)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_188_2800,
                              S1_2801: x::ll2<flted_188_2800,S1_2801>@M[Orig][LHSCase]&
                              flted_188_2800=1+n & S1_2801=union(S,{a}) & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2723:exists(v_2720:exists(S1_2645:exists(v_2642:exists(S1_2713:exists(v_2710:S1_2723= & 
  S1_2723= & S1_2713=union(S1_2723,{v_2720}) & S1_2713=union(S1_2723,
  {v_2720}) & S1_2645= & v_2642=v_2710 & a=v_2720 & S=union(S1_2645,
  {v_2642}) & S1=union(S1_2713,{v_2710})))))))) --> INS(S,S1,a),
 (exists(S1_2787:exists(v_2785:exists(S1_2645:exists(v_2642:exists(S1_2755:exists(v_2752:S1_2751=union(S1_2787,
  {v_2785}) & S1_2751=S1_2755 & v_2642=v_2752 & S1_2645=S_2677 & 
  INS(S_2677,S1_2751,a) & S=union(S1_2645,{v_2642}) & S1=union(S1_2755,
  {v_2752})))))))) --> INS(S,S1,a)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 71::
                                EXISTS(n_93,S_94,n_95,
                                S2: x::ll2<n_93,S_94>@M[Orig][LHSCase] * 
                                res::ll2<n_95,S2>@M[Orig][LHSCase]&
                                CPY(S,S2) & n_93=n & S_94=S & n_95=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 71::
                              EXISTS(n_3004,S_3005,n_3006,
                              S2_3007: x::ll2<n_3004,S_3005>@M[Orig][LHSCase] * 
                              res::ll2<n_3006,S2_3007>@M[Orig][LHSCase]&
                              n_3004=n & S_3005=S & n_3006=n & S2_3007=S & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S= & S_94=S & S_94= & S_94=)) --> CPY(S,S2),
 (exists(S1_2968:exists(v_2966:exists(S1_2965:exists(v_2963:exists(S1_2832:exists(v_2919:exists(v_2829:exists(S1_2922:exists(S_94:exists(S1_2879:exists(v_2876:(S_2836= & 
  S2_2871= | S2_2871=union(S1_2968,{v_2966}) & S_2836=union(S1_2965,
  {v_2963})) & S2=union(S1_2922,{v_2919}) & S=union(S1_2832,{v_2829}) & 
  CPY(S_2836,S2_2871) & S1_2879=S1_2832 & S_2836=S1_2832 & v_2919=v_2876 & 
  v_2829=v_2876 & S2_2871=S1_2922 & S_94=union(S1_2879,
  {v_2876}))))))))))))) --> CPY(S,S2),
 (exists(S_94:S_94= & S_94=S & S= & S2=)) --> CPY(S,S2)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::
                                EXISTS(m,S2: res::ll2<m,S2>@M[Orig][LHSCase]&
                                m<=n & FIL(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 85::
                              EXISTS(m_3345,
                              S2_3346: res::ll2<m_3345,S2_3346>@M[Orig][LHSCase]&
                              m_3345<=n & S2_3346<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S= & S2=S) --> FIL(S,S2),
 (exists(S1_3245:exists(v_3243:exists(v_3060:exists(S1_3063:exists(Anon_11:exists(v:(S2_3214= | 
  S2_3214=union(S1_3245,{v_3243})) & S=union(S1_3063,{v_3060}) & 
  FIL(S_3117,S2_3214) & S2_3214=S2 & v_3060=v & S1_3063=S_3117 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(m_3062:exists(n_3159:exists(res:exists(v_node_386_733':exists(tmp_90':exists(m_3203:exists(m:exists(m_3256:exists(m_3288:exists(n:exists(v_bool_373_731':exists(v:exists(r_3255:exists(x:exists(v_bool_372_732':exists(S1_3289:exists(v_3287:exists(S1_3257:exists(v_3254:exists(S1_3063:exists(v_3060:(S2_3204= & 
  (S1_3063=S_3160 & 1+m_3062=n & 1+n_3159=n & res=x & v_node_386_733'=x & 
  v_3060=v_3254 & tmp_90'=r_3255 & m_3203=0 & S2_3204=S1_3257 & m=1 & 
  m_3256=0 & (1+v)<=v_3254 & !(v_bool_373_731') & r_3255=null & x!=null & 
  1<=n & FIL(S_3160,S2_3204) & v_bool_372_732' | S1_3063=S_3160 & 1+
  m_3062=n & 1+n_3159=n & res=x & v_node_386_733'=x & v_3060=v_3254 & 
  tmp_90'=r_3255 & m_3203=0 & S2_3204=S1_3257 & m=1 & m_3256=0 & 
  !(v_bool_373_731') & r_3255=null & (1+v_3254)<=v & x!=null & 1<=n & 
  FIL(S_3160,S2_3204) & v_bool_372_732') | (S1_3063=S_3160 & 1+m_3062=n & 1+
  n_3159=n & res=x & v_node_386_733'=x & v_3060=v_3254 & tmp_90'=r_3255 & -1+
  m_3203=m_3288 & S2_3204=S1_3257 & -2+m=m_3288 & -1+m_3256=m_3288 & 
  0<=m_3288 & (2+m_3288)<=n & (1+v)<=v_3254 & !(v_bool_373_731') & 
  r_3255!=null & x!=null & FIL(S_3160,S2_3204) & v_bool_372_732' | 
  S1_3063=S_3160 & 1+m_3062=n & 1+n_3159=n & res=x & v_node_386_733'=x & 
  v_3060=v_3254 & tmp_90'=r_3255 & -1+m_3203=m_3288 & S2_3204=S1_3257 & -2+
  m=m_3288 & -1+m_3256=m_3288 & 0<=m_3288 & (2+m_3288)<=n & 
  !(v_bool_373_731') & (1+v_3254)<=v & r_3255!=null & x!=null & 
  FIL(S_3160,S2_3204) & v_bool_372_732') & S2_3204=union(S1_3289,
  {v_3287})) & S2=union(S1_3257,{v_3254}) & S=union(S1_3063,
  {v_3060}))))))))))))))))))))))) --> FIL(S,S2),
 (S2=S & S= & S2=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RMV2(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 78::
                                EXISTS(m,S2: res::ll2<m,S2>@M[Orig][LHSCase]&
                                m<=n & RMV2(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 78::
                              EXISTS(m_3977,
                              S2_3978: res::ll2<m_3977,S2_3978>@M[Orig][LHSCase]&
                              m_3977<=n & S2_3978<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S= & S2=S) --> RMV2(S,S2),
 (exists(S1_3881:exists(v_3879:exists(S1_3744:exists(v_3741:exists(Anon_11:exists(v:(S1_3744= | 
  S1_3744=union(S1_3881,{v_3879})) & S=union(S1_3744,{v_3741}) & 
  S1_3744=S2 & v_3741=v & Anon_11=v))))))) --> RMV2(S,S2),
 (exists(m_3743:exists(n_3801:exists(res:exists(v_node_361_756':exists(tmp_91':exists(m_3846:exists(m:exists(m_3888:exists(m_3920:exists(n:exists(v_bool_350_754':exists(v:exists(r_3887:exists(x:exists(v_bool_349_755':exists(S1_3921:exists(v_3919:exists(S1_3889:exists(v_3886:exists(S1_3744:exists(v_3741:(S2_3847= & 
  (S1_3744=S_3802 & 1+m_3743=n & 1+n_3801=n & res=x & v_node_361_756'=x & 
  v_3741=v_3886 & tmp_91'=r_3887 & m_3846=0 & S2_3847=S1_3889 & m=1 & 
  m_3888=0 & (1+v)<=v_3886 & !(v_bool_350_754') & r_3887=null & x!=null & 
  1<=n & RMV2(S_3802,S2_3847) & v_bool_349_755' | S1_3744=S_3802 & 1+
  m_3743=n & 1+n_3801=n & res=x & v_node_361_756'=x & v_3741=v_3886 & 
  tmp_91'=r_3887 & m_3846=0 & S2_3847=S1_3889 & m=1 & m_3888=0 & 
  !(v_bool_350_754') & r_3887=null & (1+v_3886)<=v & x!=null & 1<=n & 
  RMV2(S_3802,S2_3847) & v_bool_349_755') | (S1_3744=S_3802 & 1+m_3743=n & 1+
  n_3801=n & res=x & v_node_361_756'=x & v_3741=v_3886 & tmp_91'=r_3887 & -1+
  m_3846=m_3920 & S2_3847=S1_3889 & -2+m=m_3920 & -1+m_3888=m_3920 & 
  0<=m_3920 & (2+m_3920)<=n & (1+v)<=v_3886 & !(v_bool_350_754') & 
  r_3887!=null & x!=null & RMV2(S_3802,S2_3847) & v_bool_349_755' | 
  S1_3744=S_3802 & 1+m_3743=n & 1+n_3801=n & res=x & v_node_361_756'=x & 
  v_3741=v_3886 & tmp_91'=r_3887 & -1+m_3846=m_3920 & S2_3847=S1_3889 & -2+
  m=m_3920 & -1+m_3888=m_3920 & 0<=m_3920 & (2+m_3920)<=n & 
  !(v_bool_350_754') & (1+v_3886)<=v & r_3887!=null & x!=null & 
  RMV2(S_3802,S2_3847) & v_bool_349_755') & S2_3847=union(S1_3921,
  {v_3919})) & S2=union(S1_3889,{v_3886}) & S=union(S1_3744,
  {v_3741}))))))))))))))))))))))) --> RMV2(S,S2),
 (S2=S & S= & S2=) --> RMV2(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 68::
                                EXISTS(n_97,
                                S2: x::ll2<n_97,S2>@M[Orig][LHSCase]&
                                TRAV(S1,S2) & n_97=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 68::
                              EXISTS(n_4129,
                              S2_4130: x::ll2<n_4129,S2_4130>@M[Orig][LHSCase]&
                              n_4129=n & S1=S2_4130 & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S1= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_4092:exists(v_4090:exists(S1_4028:exists(v_4025:exists(v_4060:exists(S1_4063:(S2_4059= | 
  S2_4059=union(S1_4092,{v_4090})) & S2=union(S1_4063,{v_4060}) & 
  S1=union(S1_4028,{v_4025}) & TRAV(S1_4032,S2_4059) & S1_4028=S1_4032 & 
  v_4025=v_4060 & S2_4059=S1_4063))))))) --> TRAV(S1,S2),
 (S2=S1 & S1= & S2=) --> TRAV(S1,S2)]
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
                    S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(flted_102_126,
                                S2: x'::ll2<flted_102_126,S2>@M[Orig][LHSCase]&
                                flted_102_126+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::ll2<m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(flted_102_4195,
                              S2_4196: x'::ll2<flted_102_4195,S2_4196>@M[Orig][LHSCase]&
                              flted_102_4195+1=m & S2_4196<subset> S1  & 
                              0<=m&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4186:exists(v_4184:exists(v_4154:exists(S1_4157:(S1_4157= | 
  S1_4157=union(S1_4186,{v_4184})) & S1=union(S1_4157,{v_4154}) & 
  S1_4157=S2))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(S1,S,v)
!!! POST:  S1=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_91_129,
                                S1: x'::ll2<flted_91_129,S1>@M[Orig][LHSCase]&
                                flted_91_129=1+n & PUF(S1,S,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(flted_91_4236,
                              S1_4237: x'::ll2<flted_91_4236,S1_4237>@M[Orig][LHSCase]&
                              flted_91_4236=1+n & S1_4237=union(S,{v}) & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4230:exists(v_4228:exists(S1_4205:exists(v_4202:(S= | 
  S=union(S1_4230,{v_4228})) & S1=union(S1_4205,{v_4202}) & S=S1_4205 & 
  v=v_4202))))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(n_124,
                                S2: x::ll2<n_124,S2>@M[Orig][LHSCase]&
                                n_124=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::ll2<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              x::ll2<n_124,S2>@M[Orig][LHSCase]&res=x & 
                              S1=S2 & n=n_124 & 0<=n&{FLOW,(20,21)=__norm})
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
                    S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                    ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 55::ref [xs;ys]
                                EXISTS(flted_255_106,
                                S: ys'::ll2<flted_255_106,S>@M[Orig][LHSCase]&
                                flted_255_106=m+n & xs'=null & REV(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)xs::ll2<n,S1>@M[Orig][LHSCase] * 
                  ys::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 55::ref [xs;ys]
                              EXISTS(flted_255_4550,
                              S_4551: ys'::ll2<flted_255_4550,S_4551>@M[Orig][LHSCase]&
                              flted_255_4550=m+n & xs'=null & 
                              S_4551=union(S1,S2) & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4483:exists(v_4481:exists(v_4366:exists(S1_4369:exists(S1_4337:exists(v_4334:S2_4352=union(S1_4369,
  {v_4366}) & S_4446=union(S1_4483,{v_4481}) & v_4334=v_4366 & 
  S1_4337=S1_4350 & S2=S1_4369 & S_4446=S & REV(S_4446,S1_4350,S2_4352) & 
  S1=union(S1_4337,{v_4334})))))))) --> REV(S,S1,S2),
 (exists(S1_4529:exists(v_4527:(S2= | S2=union(S1_4529,{v_4527})) & S1= & 
  S2=S))) --> REV(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(S,S2,v)
!!! POST:  S2=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                    S](ex)x::node<v,t>@M[Orig] * 
                    t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                    y::ll2<j,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(k,S2: x::ll2<k,S2>@M[Orig][LHSCase]&
                                1<=k & k=1+j & SN(S,S2,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_16; Anon_17; j; 
                  S](ex)x::node<v,t>@M[Orig] * 
                  t::ll2<Anon_16,Anon_17>@M[Orig][LHSCase] * 
                  y::ll2<j,S>@M[Orig][LHSCase]&x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              EXISTS(k_4609,
                              S2_4610: x::ll2<k_4609,S2_4610>@M[Orig][LHSCase]&
                              1<=k_4609 & k_4609=1+j & S2_4610=union(S,
                              {v}) & 0<=Anon_16 & 0<=j&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4594:exists(v_4592:exists(S1_4560:exists(v_4557:(S= | 
  S=union(S1_4594,{v_4592}) | S= | S=union(S1_4594,{v_4592})) & 
  S2=union(S1_4560,{v_4557}) & S=S1_4560 & v=v_4557))))) --> SN(S,S2,v)]
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
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 96::ref [x]
                                EXISTS(flted_415_87,
                                S: x'::ll2<flted_415_87,S>@M[Orig][LHSCase]&
                                flted_415_87=n+m & SPI(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 96::ref [x]
                              EXISTS(flted_415_5253,
                              S_5254: x'::ll2<flted_415_5253,S_5254>@M[Orig][LHSCase]&
                              flted_415_5253=n+m & S_5254=union(S1,S2) & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5102:exists(v_5100:(S2= | S2=union(S1_5102,{v_5100})) & S1= & 
  S2=S))) --> SPI(S,S1,S2),
 (exists(S1_5181:exists(v_5179:exists(S1_4955:exists(S1_4990:exists(v_4952:exists(v_5118:exists(v_4987:exists(S1_5121:exists(S1_5131:exists(v_5128:(S_5068= | 
  S_5068=union(S1_5181,{v_5179})) & S=union(S1_5121,{v_5118}) & 
  S1=union(S1_4955,{v_4952}) & S2=union(S1_4990,{v_4987}) & 
  SPI(S_5068,S1_4997,S2_4999) & S1_4955=S1_4997 & S1_4990=S2_4999 & 
  v_4952=v_5118 & v_4987=v_5128 & S_5068=S1_5131 & S1_5121=union(S1_5131,
  {v_5128}) & S1_5121=union(S1_5131,{v_5128})))))))))))) --> SPI(S,S1,S2),
 (exists(S1_5226_5229:exists(v_5227:S1=S & S2= & S1=union(S1_5226_5229,
  {v_5227})))) --> SPI(S,S1,S2)]
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
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&0<a & a<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [x]
                                EXISTS(n2,n1,S1,
                                S2: x'::ll2<n1,S1>@M[Orig][LHSCase] * 
                                res::ll2<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                                0<n1 & 0<n2 & n1=a & SPLIT(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [x]
                              EXISTS(n2_5558,n1_5559,S1_5560,
                              S2_5561: x'::ll2<n1_5559,S1_5560>@M[Orig][LHSCase] * 
                              res::ll2<n2_5558,S2_5561>@M[Orig][LHSCase]&
                              n=n2_5558+n1_5559 & 0<n1_5559 & 0<n2_5558 & 
                              n1_5559=a & union(S1_5560,S2_5561)=S & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5416:exists(v_5414:exists(S1_5293:exists(v_5290:exists(S1_5387:exists(v_5384:S1_5387= & 
  S1_5387= & S1_5293=union(S1_5416,{v_5414}) & v_5290=v_5384 & S1_5293=S2 & 
  S=union(S1_5293,{v_5290}) & S1=union(S1_5387,
  {v_5384})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_5519:exists(v_5517:exists(S1_5522:exists(v_5520:exists(S1_5333:exists(v_5330:exists(S1_5436:exists(v_5433:S1_5429=union(S1_5519,
  {v_5517}) & S2_5430=union(S1_5522,{v_5520}) & S1_5429=S1_5436 & 
  v_5330=v_5433 & S1_5333=S_5335 & S2_5430=S2 & 
  SPLIT(S_5335,S1_5429,S2_5430) & S=union(S1_5333,{v_5330}) & 
  S1=union(S1_5436,{v_5433})))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                    y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_132,n_133,S3,
                                S4: x'::ll2<m_132,S3>@M[Orig][LHSCase] * 
                                y'::ll2<n_133,S4>@M[Orig][LHSCase]&m_132=m & 
                                n_133=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::ll2<n,S1>@M[Orig][LHSCase] * 
                  y::ll2<m,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::ll2<m_132,S3>@M[Orig][LHSCase] * 
                              y'::ll2<n_133,S4>@M[Orig][LHSCase]&y=x' & 
                              y'=x & S2=S3 & S1=S4 & m=m_132 & n=n_133 & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (162,13)  (162,4)  (241,4)  (241,11)  (246,4)  (246,11)  (245,10)  (245,4)  (244,8)  (244,12)  (244,4)  (244,4) )

Total verification time: 25.34 second(s)
	Time spent in main process: 2.63 second(s)
	Time spent in child processes: 22.71 second(s)
