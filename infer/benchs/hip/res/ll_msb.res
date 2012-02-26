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
                              
                              x'::ll2<n_131,S4>@M[Orig][LHSCase]&n_131=0 & 
                              n=0 & x'=null & S4= & 0<=m&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(S_1707: x'::ll2<n_131,S4>@M[Orig][LHSCase]&
                                 S4=S_1707 & n_131=n & 1<=n & 
                                 534::forall(_x:_x <notin> S_1707  | _x=v) & 
                                 0<=m&{FLOW,(20,21)=__norm})
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
                              EXISTS(m_1954,
                              S1_1955: x::ll2<m_1954,S1_1955>@M[Orig][LHSCase]&
                              S1_1955<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1892:exists(v_1890:exists(v_1743:exists(v_1852:exists(S1_1855:exists(S1_1746:exists(S1_1776:exists(v_1773:(S1_1776= | 
  S1_1776=union(S1_1892,{v_1890})) & S1=union(S1_1855,{v_1852}) & 
  S=union(S1_1746,{v_1743}) & v_1743=v_1852 & S1_1776=S1_1855 & 
  S1_1746=union(S1_1776,{v_1773})))))))))) --> DEL(S,S1),
 (exists(S1_1933:exists(v_1931:exists(S1_1804:exists(v_1801:exists(v_1904:exists(S1_1907:(S1_1902= | 
  S1_1902=union(S1_1933,{v_1931})) & S1=union(S1_1907,{v_1904}) & 
  S=union(S1_1804,{v_1801}) & DEL(S_1817,S1_1902) & S1_1804=S_1817 & 
  v_1801=v_1904 & S1_1902=S1_1907))))))) --> DEL(S,S1)]
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
                              EXISTS(m_2195,
                              S1_2196: res::ll2<m_2195,S1_2196>@M[Orig][LHSCase]&
                              m_2195<=n & (S1_2196=S & a <notin> S  | 
                              S1_2196<subset> S  & a <in> S ) & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S= & S1=S) --> DEL2(a,S,S1),
 (S1=S & S= & S1=) --> DEL2(a,S,S1),
 (exists(S1_2107:exists(v_2105:exists(S1_1992:exists(v_1989:(S1_1992= | 
  S1_1992=union(S1_2107,{v_2105})) & S=union(S1_1992,{v_1989}) & 
  S1_1992=S1 & a=v_1989))))) --> DEL2(a,S,S1),
 (exists(m_1991:exists(n_2029:exists(v_node_224_909':exists(v_node_224_2117:exists(m_2115:exists(m:exists(m_2120:exists(m_2152:exists(n:exists(v_bool_220_911':exists(v_bool_223_910':exists(x:exists(r_2119:exists(res:exists(S1_2153:exists(v_2151:exists(S1_2121:exists(v_2118:exists(S1_1992:exists(v_1989:(S1_2116= & 
  (S1_1992=S_2030 & 1+m_1991=n & 1+n_2029=n & v_node_224_909'=res & 
  v_1989=v_2118 & v_node_224_2117=r_2119 & m_2115=0 & S1_2116=S1_2121 & 
  m=1 & m_2120=0 & !(v_bool_220_911') & (1+a)<=v_2118 & !(v_bool_223_910') & 
  r_2119=null & x!=null & res!=null & 1<=n & DEL2(a,S_2030,S1_2116) | 
  S1_1992=S_2030 & 1+m_1991=n & 1+n_2029=n & v_node_224_909'=res & 
  v_1989=v_2118 & v_node_224_2117=r_2119 & m_2115=0 & S1_2116=S1_2121 & 
  m=1 & m_2120=0 & !(v_bool_220_911') & !(v_bool_223_910') & r_2119=null & 
  (1+v_2118)<=a & x!=null & res!=null & 1<=n & DEL2(a,S_2030,S1_2116)) | 
  (S1_1992=S_2030 & 1+m_1991=n & 1+n_2029=n & v_node_224_909'=res & 
  v_1989=v_2118 & v_node_224_2117=r_2119 & -1+m_2115=m_2152 & 
  S1_2116=S1_2121 & -2+m=m_2152 & -1+m_2120=m_2152 & 0<=m_2152 & (2+
  m_2152)<=n & !(v_bool_220_911') & (1+a)<=v_2118 & !(v_bool_223_910') & 
  x!=null & r_2119!=null & res!=null & DEL2(a,S_2030,S1_2116) | 
  S1_1992=S_2030 & 1+m_1991=n & 1+n_2029=n & v_node_224_909'=res & 
  v_1989=v_2118 & v_node_224_2117=r_2119 & -1+m_2115=m_2152 & 
  S1_2116=S1_2121 & -2+m=m_2152 & -1+m_2120=m_2152 & 0<=m_2152 & (2+
  m_2152)<=n & !(v_bool_220_911') & !(v_bool_223_910') & (1+v_2118)<=a & 
  x!=null & r_2119!=null & res!=null & DEL2(a,S_2030,S1_2116)) & 
  S1_2116=union(S1_2153,{v_2151})) & S1=union(S1_2121,{v_2118}) & 
  S=union(S1_1992,{v_1989})))))))))))))))))))))) --> DEL2(a,S,S1)]
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
                              or EXISTS(Anon_2436,
                                 m_2437: res::node<m_2437,Anon_2436>@M[Orig]&
                                 v<m_2437 & {m_2437}<subset> S  & 0<=n&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(S1_2416:exists(v_2414:exists(S1_2327:exists(v:exists(v_2324:(S1_2327= | 
  S1_2327=union(S1_2416,{v_2414})) & S=union(S1_2327,{v_2324}) & (1+v)<=m & 
  v_2324=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2327:exists(v_2324:v_2324<=v & S1_2327=S_2374 & 
  m_2426=m & (1+v)<=m & FGE(S_2374,m_2426) & S=union(S1_2327,
  {v_2324}))))) --> FGE(S,m)]
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
                              EXISTS(flted_138_2521,flted_138_2522,S1_2523,
                              S2_2524: x'::ll2<flted_138_2522,S1_2523>@M[Orig][LHSCase] * 
                              res::ll2<flted_138_2521,S2_2524>@M[Orig][LHSCase]&
                              flted_138_2522=1 & flted_138_2521+1=n & 
                              union(S1_2523,S2_2524)=S & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2512:exists(v_2510:exists(S1_2470:exists(v_2467:exists(v_2478:exists(S1_2481:(S1_2470= | 
  S1_2470=union(S1_2512,{v_2510})) & S1=union(S1_2481,{v_2478}) & 
  S=union(S1_2470,{v_2467}) & S1_2470=S2 & v_2467=v_2478 & S1_2481= & 
  S1_2481=))))))) --> GN(S,S1,S2)]
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
                              EXISTS(flted_178_2620,
                              S2_2621: res::ll2<flted_178_2620,S2_2621>@M[Orig][LHSCase]&
                              flted_178_2620+2=n & S2_2621<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2607:exists(v_2605:exists(v_2545:exists(S1_2548:exists(S1_2578:exists(v_2575:(S1_2578= | 
  S1_2578=union(S1_2607,{v_2605})) & S=union(S1_2548,{v_2545}) & 
  S1_2578=S2 & S1_2548=union(S1_2578,{v_2575})))))))) --> GNN(S,S2)]
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
                              EXISTS(flted_188_2801,
                              S1_2802: x::ll2<flted_188_2801,S1_2802>@M[Orig][LHSCase]&
                              flted_188_2801=1+n & S1_2802=union(S,{a}) & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2724:exists(v_2721:exists(S1_2646:exists(v_2643:exists(S1_2714:exists(v_2711:S1_2724= & 
  S1_2724= & S1_2714=union(S1_2724,{v_2721}) & S1_2714=union(S1_2724,
  {v_2721}) & S1_2646= & v_2643=v_2711 & a=v_2721 & S=union(S1_2646,
  {v_2643}) & S1=union(S1_2714,{v_2711})))))))) --> INS(S,S1,a),
 (exists(S1_2788:exists(v_2786:exists(S1_2646:exists(v_2643:exists(S1_2756:exists(v_2753:S1_2752=union(S1_2788,
  {v_2786}) & S1_2752=S1_2756 & v_2643=v_2753 & S1_2646=S_2678 & 
  INS(S_2678,S1_2752,a) & S=union(S1_2646,{v_2643}) & S1=union(S1_2756,
  {v_2753})))))))) --> INS(S,S1,a)]
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
                              EXISTS(n_3005,S_3006,n_3007,
                              S2_3008: x::ll2<n_3005,S_3006>@M[Orig][LHSCase] * 
                              res::ll2<n_3007,S2_3008>@M[Orig][LHSCase]&
                              n_3005=n & S_3006=S & n_3007=n & S2_3008=S & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_94:S2= & S= & S_94=S & S_94= & S_94=)) --> CPY(S,S2),
 (exists(S1_2969:exists(v_2967:exists(S1_2966:exists(v_2964:exists(S1_2833:exists(v_2920:exists(v_2830:exists(S1_2923:exists(S_94:exists(S1_2880:exists(v_2877:(S_2837= & 
  S2_2872= | S2_2872=union(S1_2969,{v_2967}) & S_2837=union(S1_2966,
  {v_2964})) & S2=union(S1_2923,{v_2920}) & S=union(S1_2833,{v_2830}) & 
  CPY(S_2837,S2_2872) & S1_2880=S1_2833 & S_2837=S1_2833 & v_2920=v_2877 & 
  v_2830=v_2877 & S2_2872=S1_2923 & S_94=union(S1_2880,
  {v_2877}))))))))))))) --> CPY(S,S2),
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
                              EXISTS(m_3346,
                              S2_3347: res::ll2<m_3346,S2_3347>@M[Orig][LHSCase]&
                              m_3346<=n & S2_3347<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S= & S2=S) --> FIL(S,S2),
 (exists(S1_3246:exists(v_3244:exists(v_3061:exists(S1_3064:exists(Anon_11:exists(v:(S2_3215= | 
  S2_3215=union(S1_3246,{v_3244})) & S=union(S1_3064,{v_3061}) & 
  FIL(S_3118,S2_3215) & S2_3215=S2 & v_3061=v & S1_3064=S_3118 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(m_3063:exists(n_3160:exists(res:exists(v_node_386_733':exists(tmp_90':exists(m_3204:exists(m:exists(m_3257:exists(m_3289:exists(n:exists(v_bool_373_731':exists(v:exists(r_3256:exists(x:exists(v_bool_372_732':exists(S1_3290:exists(v_3288:exists(S1_3258:exists(v_3255:exists(S1_3064:exists(v_3061:(S2_3205= & 
  (S1_3064=S_3161 & 1+m_3063=n & 1+n_3160=n & res=x & v_node_386_733'=x & 
  v_3061=v_3255 & tmp_90'=r_3256 & m_3204=0 & S2_3205=S1_3258 & m=1 & 
  m_3257=0 & (1+v)<=v_3255 & !(v_bool_373_731') & r_3256=null & x!=null & 
  1<=n & FIL(S_3161,S2_3205) & v_bool_372_732' | S1_3064=S_3161 & 1+
  m_3063=n & 1+n_3160=n & res=x & v_node_386_733'=x & v_3061=v_3255 & 
  tmp_90'=r_3256 & m_3204=0 & S2_3205=S1_3258 & m=1 & m_3257=0 & 
  !(v_bool_373_731') & r_3256=null & (1+v_3255)<=v & x!=null & 1<=n & 
  FIL(S_3161,S2_3205) & v_bool_372_732') | (S1_3064=S_3161 & 1+m_3063=n & 1+
  n_3160=n & res=x & v_node_386_733'=x & v_3061=v_3255 & tmp_90'=r_3256 & -1+
  m_3204=m_3289 & S2_3205=S1_3258 & -2+m=m_3289 & -1+m_3257=m_3289 & 
  0<=m_3289 & (2+m_3289)<=n & (1+v)<=v_3255 & !(v_bool_373_731') & 
  r_3256!=null & x!=null & FIL(S_3161,S2_3205) & v_bool_372_732' | 
  S1_3064=S_3161 & 1+m_3063=n & 1+n_3160=n & res=x & v_node_386_733'=x & 
  v_3061=v_3255 & tmp_90'=r_3256 & -1+m_3204=m_3289 & S2_3205=S1_3258 & -2+
  m=m_3289 & -1+m_3257=m_3289 & 0<=m_3289 & (2+m_3289)<=n & 
  !(v_bool_373_731') & (1+v_3255)<=v & r_3256!=null & x!=null & 
  FIL(S_3161,S2_3205) & v_bool_372_732') & S2_3205=union(S1_3290,
  {v_3288})) & S2=union(S1_3258,{v_3255}) & S=union(S1_3064,
  {v_3061}))))))))))))))))))))))) --> FIL(S,S2),
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
                              EXISTS(m_3978,
                              S2_3979: res::ll2<m_3978,S2_3979>@M[Orig][LHSCase]&
                              m_3978<=n & S2_3979<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S= & S2=S) --> RMV2(S,S2),
 (exists(S1_3882:exists(v_3880:exists(S1_3745:exists(v_3742:exists(Anon_11:exists(v:(S1_3745= | 
  S1_3745=union(S1_3882,{v_3880})) & S=union(S1_3745,{v_3742}) & 
  S1_3745=S2 & v_3742=v & Anon_11=v))))))) --> RMV2(S,S2),
 (exists(m_3744:exists(n_3802:exists(res:exists(v_node_361_756':exists(tmp_91':exists(m_3847:exists(m:exists(m_3889:exists(m_3921:exists(n:exists(v_bool_350_754':exists(v:exists(r_3888:exists(x:exists(v_bool_349_755':exists(S1_3922:exists(v_3920:exists(S1_3890:exists(v_3887:exists(S1_3745:exists(v_3742:(S2_3848= & 
  (S1_3745=S_3803 & 1+m_3744=n & 1+n_3802=n & res=x & v_node_361_756'=x & 
  v_3742=v_3887 & tmp_91'=r_3888 & m_3847=0 & S2_3848=S1_3890 & m=1 & 
  m_3889=0 & (1+v)<=v_3887 & !(v_bool_350_754') & r_3888=null & x!=null & 
  1<=n & RMV2(S_3803,S2_3848) & v_bool_349_755' | S1_3745=S_3803 & 1+
  m_3744=n & 1+n_3802=n & res=x & v_node_361_756'=x & v_3742=v_3887 & 
  tmp_91'=r_3888 & m_3847=0 & S2_3848=S1_3890 & m=1 & m_3889=0 & 
  !(v_bool_350_754') & r_3888=null & (1+v_3887)<=v & x!=null & 1<=n & 
  RMV2(S_3803,S2_3848) & v_bool_349_755') | (S1_3745=S_3803 & 1+m_3744=n & 1+
  n_3802=n & res=x & v_node_361_756'=x & v_3742=v_3887 & tmp_91'=r_3888 & -1+
  m_3847=m_3921 & S2_3848=S1_3890 & -2+m=m_3921 & -1+m_3889=m_3921 & 
  0<=m_3921 & (2+m_3921)<=n & (1+v)<=v_3887 & !(v_bool_350_754') & 
  r_3888!=null & x!=null & RMV2(S_3803,S2_3848) & v_bool_349_755' | 
  S1_3745=S_3803 & 1+m_3744=n & 1+n_3802=n & res=x & v_node_361_756'=x & 
  v_3742=v_3887 & tmp_91'=r_3888 & -1+m_3847=m_3921 & S2_3848=S1_3890 & -2+
  m=m_3921 & -1+m_3889=m_3921 & 0<=m_3921 & (2+m_3921)<=n & 
  !(v_bool_350_754') & (1+v_3887)<=v & r_3888!=null & x!=null & 
  RMV2(S_3803,S2_3848) & v_bool_349_755') & S2_3848=union(S1_3922,
  {v_3920})) & S2=union(S1_3890,{v_3887}) & S=union(S1_3745,
  {v_3742}))))))))))))))))))))))) --> RMV2(S,S2),
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
                              EXISTS(n_4130,
                              S2_4131: x::ll2<n_4130,S2_4131>@M[Orig][LHSCase]&
                              n_4130=n & S1=S2_4131 & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S1= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_4093:exists(v_4091:exists(S1_4029:exists(v_4026:exists(v_4061:exists(S1_4064:(S2_4060= | 
  S2_4060=union(S1_4093,{v_4091})) & S2=union(S1_4064,{v_4061}) & 
  S1=union(S1_4029,{v_4026}) & TRAV(S1_4033,S2_4060) & S1_4029=S1_4033 & 
  v_4026=v_4061 & S2_4060=S1_4064))))))) --> TRAV(S1,S2),
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
                              EXISTS(flted_102_4196,
                              S2_4197: x'::ll2<flted_102_4196,S2_4197>@M[Orig][LHSCase]&
                              flted_102_4196+1=m & S2_4197<subset> S1  & 
                              0<=m&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4187:exists(v_4185:exists(v_4155:exists(S1_4158:(S1_4158= | 
  S1_4158=union(S1_4187,{v_4185})) & S1=union(S1_4158,{v_4155}) & 
  S1_4158=S2))))) --> PF(S1,S2)]
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
                              EXISTS(flted_91_4237,
                              S1_4238: x'::ll2<flted_91_4237,S1_4238>@M[Orig][LHSCase]&
                              flted_91_4237=1+n & S1_4238=union(S,{v}) & 
                              0<=n&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4231:exists(v_4229:exists(S1_4206:exists(v_4203:(S= | 
  S=union(S1_4231,{v_4229})) & S1=union(S1_4206,{v_4203}) & S=S1_4206 & 
  v=v_4203))))) --> PUF(S1,S,v)]
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
                              x::ll2<n_124,S2>@M[Orig][LHSCase]&x=res & 
                              S2=S1 & n_124=n & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
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
                              EXISTS(flted_255_4551,
                              S_4552: ys'::ll2<flted_255_4551,S_4552>@M[Orig][LHSCase]&
                              flted_255_4551=m+n & xs'=null & 
                              S_4552=union(S1,S2) & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4484:exists(v_4482:exists(v_4367:exists(S1_4370:exists(S1_4338:exists(v_4335:S2_4353=union(S1_4370,
  {v_4367}) & S_4447=union(S1_4484,{v_4482}) & v_4335=v_4367 & 
  S1_4338=S1_4351 & S2=S1_4370 & S_4447=S & REV(S_4447,S1_4351,S2_4353) & 
  S1=union(S1_4338,{v_4335})))))))) --> REV(S,S1,S2),
 (exists(S1_4530:exists(v_4528:(S2= | S2=union(S1_4530,{v_4528})) & S1= & 
  S2=S))) --> REV(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              EXISTS(k_4610,S2_4611: true&1<=k_4610 & 
                              k_4610=1+j & S2_4611=union(S,{v}) & 
                              0<=Anon_16 & 0<=j&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4595:exists(v_4593:exists(S1_4561:exists(v_4558:(S= | 
  S=union(S1_4595,{v_4593}) | S= | S=union(S1_4595,{v_4593})) & 
  S2=union(S1_4561,{v_4558}) & S=S1_4561 & v=v_4558))))) --> SN(S,S2,v)]
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
                              EXISTS(flted_415_5254,
                              S_5255: x'::ll2<flted_415_5254,S_5255>@M[Orig][LHSCase]&
                              flted_415_5254=n+m & S_5255=union(S1,S2) & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5103:exists(v_5101:(S2= | S2=union(S1_5103,{v_5101})) & S1= & 
  S2=S))) --> SPI(S,S1,S2),
 (exists(S1_5182:exists(v_5180:exists(S1_4956:exists(S1_4991:exists(v_4953:exists(v_5119:exists(v_4988:exists(S1_5122:exists(S1_5132:exists(v_5129:(S_5069= | 
  S_5069=union(S1_5182,{v_5180})) & S=union(S1_5122,{v_5119}) & 
  S1=union(S1_4956,{v_4953}) & S2=union(S1_4991,{v_4988}) & 
  SPI(S_5069,S1_4998,S2_5000) & S1_4956=S1_4998 & S1_4991=S2_5000 & 
  v_4953=v_5119 & v_4988=v_5129 & S_5069=S1_5132 & S1_5122=union(S1_5132,
  {v_5129}) & S1_5122=union(S1_5132,{v_5129})))))))))))) --> SPI(S,S1,S2),
 (exists(S1_5227_5230:exists(v_5228:S1=S & S2= & S1=union(S1_5227_5230,
  {v_5228})))) --> SPI(S,S1,S2)]
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
                              EXISTS(n2_5559,n1_5560,S1_5561,
                              S2_5562: x'::ll2<n1_5560,S1_5561>@M[Orig][LHSCase] * 
                              res::ll2<n2_5559,S2_5562>@M[Orig][LHSCase]&
                              n=n2_5559+n1_5560 & 0<n1_5560 & 0<n2_5559 & 
                              n1_5560=a & union(S1_5561,S2_5562)=S & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5417:exists(v_5415:exists(S1_5294:exists(v_5291:exists(S1_5388:exists(v_5385:S1_5388= & 
  S1_5388= & S1_5294=union(S1_5417,{v_5415}) & v_5291=v_5385 & S1_5294=S2 & 
  S=union(S1_5294,{v_5291}) & S1=union(S1_5388,
  {v_5385})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_5520:exists(v_5518:exists(S1_5523:exists(v_5521:exists(S1_5334:exists(v_5331:exists(S1_5437:exists(v_5434:S1_5430=union(S1_5520,
  {v_5518}) & S2_5431=union(S1_5523,{v_5521}) & S1_5430=S1_5437 & 
  v_5331=v_5434 & S1_5334=S_5336 & S2_5431=S2 & 
  SPLIT(S_5336,S1_5430,S2_5431) & S=union(S1_5334,{v_5331}) & 
  S1=union(S1_5437,{v_5434})))))))))) --> SPLIT(S,S1,S2)]
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
                              y'::ll2<n_133,S4>@M[Orig][LHSCase]&x'=y & 
                              x=y' & S3=S2 & S4=S1 & m_132=m & n_133=n & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


12 false contexts at: ( (162,13)  (162,4)  (241,4)  (241,11)  (246,4)  (246,11)  (245,10)  (245,4)  (244,8)  (244,12)  (244,4)  (244,4) )

Total verification time: 24.93 second(s)
	Time spent in main process: 3.07 second(s)
	Time spent in child processes: 21.86 second(s)
