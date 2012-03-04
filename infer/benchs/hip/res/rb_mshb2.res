/usr/local/bin/mona

Processing file "rb_mshb2.ss"
Parsing rb_mshb2.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure case_2$node~node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  ROT2(S5,S1,S2,S3,S4)
!!! POST:  S5=union(S1,S2,{0},S3,S4,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT2]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; S3; nd; bha; 
                    S4](ex)EXISTS(bha_158,bha_159,bha_160,flted_42_154,
                    flted_42_155,flted_42_156,
                    flted_42_157: a::rb1<na,flted_42_157,bha,S1>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    b::rb1<nb,flted_42_156,bha_158,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    c::rb1<nc,flted_42_155,bha_159,S3>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    d::rb1<nd,flted_42_154,bha_160,S4>@M[Orig][LHSCase]@ rem br[{159,157}]&
                    (
                    ([flted_42_157=0][flted_42_156=0][flted_42_155=0]
                     [flted_42_154=0]
                     [bha=bha_160 & bha=bha_159 & bha=bha_158 & 1<=bha_160]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(flted_43_151,flted_43_152,
                                flted_43_153,
                                S5: res::rb1<flted_43_153,flted_43_152,flted_43_151,S5>@M[Orig][LHSCase]@ rem br[{157}]&
                                (
                                ([flted_43_153=3+na+nb+nc+nd][flted_43_152=0]
                                 [1!=flted_43_151 & -1+flted_43_151=bha]
                                 [S5!=() & ROT2(S5,S1,S2,S3,S4)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; S3; nd; bha; 
                  S4](ex)a::rb1<na,flted_42_157,bha,S1>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  b::rb1<nb,flted_42_156,bha_158,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  c::rb1<nc,flted_42_155,bha_159,S3>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  d::rb1<nd,flted_42_154,bha_160,S4>@M[Orig][LHSCase]@ rem br[{159,157}]&
                  (
                  ([bha_159=bha & bha_159=bha_160 & bha_159=bha_158 & 
                     1<=bha_159]
                   [0=flted_42_157][0=flted_42_156][0=flted_42_155]
                   [0=flted_42_154]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              EXISTS(flted_43_1646,flted_43_1647,
                              flted_43_1648,
                              S5_1649: res::rb1<flted_43_1648,flted_43_1647,flted_43_1646,S5_1649>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S5_1649!=() & S5_1649=union(S1,S2,{0},S3,S4,
                                 {0},{0})]
                               [null!=res]
                               [1!=flted_43_1646 & 1<=bha & -1+
                                 flted_43_1646=bha]
                               [0=flted_43_1647]
                               [flted_43_1648=3+na+nb+nc+nd & 0<=na & 
                                 0<=nd & 0<=nb & 0<=nc]
                               [1<=bha_160]
                               [0<=flted_42_154 & flted_42_154<=1]
                               [1<=bha_159]
                               [0<=flted_42_155 & flted_42_155<=1]
                               [1<=bha_158]
                               [0<=flted_42_156 & flted_42_156<=1]
                               [0<=flted_42_157 & flted_42_157<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1494:exists(v_1523:exists(S4_1614:exists(S3_1499:exists(S2_1496:exists(S2_1531:exists(S1_1527:v_1523=0 & 
  S4_1614=union(S1_1494,S2_1496,S3_1499,{0},{0}) & S1_1494=union(S1_1527,
  S2_1531,{v_1523}) & S4_1614=S5 & S4=S3_1499 & S3=S2_1496 & S2=S2_1531 & 
  S1=S1_1527)))))))) --> ROT2(S5,S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! REL :  ROT2R(S5,S1,S2,S3,S4)
!!! POST:  S5=union(S1,S2,S3,S4,{0},{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT2R]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; S3; nd; bha; 
                    S4](ex)EXISTS(bha_94,bha_95,bha_96,flted_82_90,
                    flted_82_91,flted_82_92,
                    flted_82_93: a::rb1<na,flted_82_93,bha,S1>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    b::rb1<nb,flted_82_92,bha_94,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    c::rb1<nc,flted_82_91,bha_95,S3>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    d::rb1<nd,flted_82_90,bha_96,S4>@M[Orig][LHSCase]@ rem br[{159,157}]&
                    (
                    ([flted_82_93=0][flted_82_92=0][flted_82_91=0]
                     [flted_82_90=0]
                     [bha=bha_96 & bha=bha_95 & bha=bha_94 & 1<=bha_96]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 10::
                                EXISTS(flted_83_87,flted_83_88,flted_83_89,
                                S5: res::rb1<flted_83_89,flted_83_88,flted_83_87,S5>@M[Orig][LHSCase]@ rem br[{157}]&
                                (
                                ([flted_83_89=3+na+nb+nc+nd][flted_83_88=0]
                                 [1!=flted_83_87 & -1+flted_83_87=bha]
                                 [S5!=() & ROT2R(S5,S1,S2,S3,S4)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; S3; nd; bha; 
                  S4](ex)a::rb1<na,flted_82_93,bha,S1>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  b::rb1<nb,flted_82_92,bha_94,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  c::rb1<nc,flted_82_91,bha_95,S3>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  d::rb1<nd,flted_82_90,bha_96,S4>@M[Orig][LHSCase]@ rem br[{159,157}]&
                  (
                  ([bha_95=bha & bha_95=bha_96 & bha_95=bha_94 & 1<=bha_95]
                   [0=flted_82_93][0=flted_82_92][0=flted_82_91]
                   [0=flted_82_90]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 10::
                              EXISTS(flted_83_1812,flted_83_1813,
                              flted_83_1814,
                              S5_1815: res::rb1<flted_83_1814,flted_83_1813,flted_83_1812,S5_1815>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S5_1815!=() & S5_1815=union(S1,S2,S3,S4,{0},
                                 {0},{0})]
                               [null!=res]
                               [1!=flted_83_1812 & 1<=bha & -1+
                                 flted_83_1812=bha]
                               [0=flted_83_1813]
                               [flted_83_1814=3+na+nb+nc+nd & 0<=na & 
                                 0<=nd & 0<=nb & 0<=nc]
                               [1<=bha_96][0<=flted_82_90 & flted_82_90<=1]
                               [1<=bha_95][0<=flted_82_91 & flted_82_91<=1]
                               [1<=bha_94][0<=flted_82_92 & flted_82_92<=1]
                               [0<=flted_82_93 & flted_82_93<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S3_1676:exists(v_1703:exists(S4_1780:exists(S1_1671:exists(S2_1673:exists(S2_1711:exists(S1_1707:v_1703=0 & 
  S4_1780=union(S1_1671,S2_1673,S3_1676,{0},{0}) & S3_1676=union(S1_1707,
  S2_1711,{v_1703}) & S4_1780=S5 & S1=S1_1671 & S2_1673=S2 & S4=S2_1711 & 
  S3=S1_1707)))))))) --> ROT2R(S5,S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure is_black$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  BLACK2(S2,S)
!!! POST:  S=S2
!!! PRE :  true
!!! REL :  BLACK1(S1,S)
!!! POST:  S=S1
!!! PRE :  true
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! OLD SPECS: ((None,[]),EInfer [BLACK1,BLACK2]
              EBase exists (Expl)(Impl)[n; cl; bh; 
                    S](ex)x::rb1<n,cl,bh,S>@M[Orig][LHSCase]@ rem br[{159,158,157}]&
                    (([true][1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::
                                
                                EXISTS(n_43,cl_44,bh_45,
                                S1: x::rb1<n_43,cl_44,bh_45,S1>@M[Orig][LHSCase]@ rem br[{158}]&
                                (
                                ([!(res)][S1!=() & BLACK1(S1,S)]
                                 [n=n_43 & 0!=n_43][cl=cl_44 & cl=1]
                                 [bh=bh_45 & 1<=bh_45][null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(n_46,cl_47,bh_48,
                                   S2: x::rb1<n_46,cl_47,bh_48,S2>@M[Orig][LHSCase]@ rem br[{159,157}]&
                                   (
                                   ([res][BLACK2(S2,S)][n=n_46]
                                    [cl=cl_47 & cl=0][bh=bh_48 & 1<=bh_48]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; cl; bh; 
                  S](ex)x::rb1<n,cl,bh,S>@M[Orig][LHSCase]@ rem br[{159,158,157}]&
                  (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 17::
                              
                              EXISTS(n_2250,cl_2251,bh_2252,
                              S1_2253: x::rb1<n_2250,cl_2251,bh_2252,S1_2253>@M[Orig][LHSCase]@ rem br[{158}]&
                              (
                              ([S=S1_2253 & S1_2253!=()][null!=x]
                               [bh=bh_2252 & 1<=bh]
                               [1=cl & 1=cl_2251 & 0<=cl & cl<=1]
                               [n=n_2250 & 0!=n_2250 & 0<=n][!(res)]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n_2254,cl_2255,bh_2256,
                                 S2_2257: x::rb1<n_2254,cl_2255,bh_2256,S2_2257>@M[Orig][LHSCase]@ rem br[{159,157}]&
                                 (
                                 ([S=S2_2257][bh=bh_2256 & 1<=bh]
                                  [0=cl & 0=cl_2255 & 0<=cl & cl<=1]
                                  [n=n_2254 & 0<=n][res]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S2=S) --> BLACK2(S2,S),
 (S=S2 & S2=) --> BLACK2(S2,S),
 (exists(l_1928:exists(l_2027:exists(r_1933:exists(r_2032:exists(cl:exists(nr_2033:exists(n:exists(bh_48_2066:exists(bh_48:exists(bhl_2030:exists(bh:exists(bhl_1931:exists(flted_13_1926:exists(cl_47:exists(Anon_2029:exists(Anon_2034:exists(bhr_1936:exists(res:exists(nr_1934:exists(nl_1929:exists(nl_2028:exists(Anon_1930:exists(Anon_1935:exists(v_bool_136_795':exists(x:exists(bhr_2035:exists(v_boolean_141_792':exists(v_bool_140_794':exists(n_46:exists(S1_2031:exists(S2_2036:exists(v_2026:exists(S1_1932:exists(S2_1937:exists(v_1927:(l_1928=l_2027 & 
  r_1933=r_2032 & cl=0 & 1+nl_2028+nr_2033=n_46 & n=n_46 & S2_2036=S2_1937 & 
  v_2026=v_1927 & S1_1932=S1_2031 & -1+bh_48_2066=bhr_2035 & -1+
  bh_48=bhr_2035 & bhl_2030=bhr_2035 & -1+bh=bhr_2035 & bhl_1931=bhr_2035 & 
  flted_13_1926=0 & cl_47=0 & Anon_2029=Anon_1930 & Anon_2034=Anon_1935 & 
  bhr_1936=bhr_2035 & res=v_boolean_141_792' & 1+nl_2028+nr_1934=n_46 & 
  nl_1929=nl_2028 & 0<=Anon_1930 & Anon_1930<=1 & 0<=Anon_1935 & 
  Anon_1935<=1 & n_46<=-1 & v_bool_136_795'<=0 & x!=null & 1<=bhr_2035 & 
  1<=v_boolean_141_792' & 1<=v_bool_140_794' | l_1928=l_2027 & 
  r_1933=r_2032 & cl=0 & 1+nl_2028+nr_2033=n_46 & n=n_46 & S2_2036=S2_1937 & 
  v_2026=v_1927 & S1_1932=S1_2031 & -1+bh_48_2066=bhr_2035 & -1+
  bh_48=bhr_2035 & bhl_2030=bhr_2035 & -1+bh=bhr_2035 & bhl_1931=bhr_2035 & 
  flted_13_1926=0 & cl_47=0 & Anon_2029=Anon_1930 & Anon_2034=Anon_1935 & 
  bhr_1936=bhr_2035 & res=v_boolean_141_792' & 1+nl_2028+nr_1934=n_46 & 
  nl_1929=nl_2028 & 0<=Anon_1930 & Anon_1930<=1 & 0<=Anon_1935 & 
  Anon_1935<=1 & v_bool_136_795'<=0 & x!=null & 1<=bhr_2035 & 
  1<=v_boolean_141_792' & 1<=v_bool_140_794' & 1<=n_46) & S2=union(S1_2031,
  S2_2036,{v_2026}) & S!=() & S=union(S1_1932,S2_1937,
  {v_1927}))))))))))))))))))))))))))))))))))))) --> BLACK2(S2,S),
 (exists(l_1905:exists(l_2094:exists(r_1909:exists(r_2098:exists(flted_12_1902:exists(flted_12_1901:exists(cl:exists(nr_2099:exists(n:exists(bhr_2100:exists(bh:exists(bh_45:exists(bhr_1911:exists(flted_12_1903:exists(cl_44:exists(res:exists(bhl_1907:exists(nr_1910:exists(nl_1906:exists(nl_2095:exists(v_bool_140_794':exists(v_bool_136_795':exists(v_boolean_143_793':exists(x:exists(bhl_2096:exists(n_43:exists(S1_1908:exists(S2_1912:exists(v_1904:exists(S1_2097:exists(S2_2101:exists(v_2093:(l_1905=l_2094 & 
  r_1909=r_2098 & flted_12_1902=0 & flted_12_1901=0 & cl=1 & 1+nl_2095+
  nr_2099=n_43 & n=n_43 & bhr_2100=bhl_2096 & bh=bhl_2096 & bh_45=bhl_2096 & 
  bhr_1911=bhl_2096 & S2_2101=S2_1912 & v_2093=v_1904 & S1_1908=S1_2097 & 
  flted_12_1903=1 & cl_44=1 & res=v_boolean_143_793' & bhl_1907=bhl_2096 & 1+
  nl_2095+nr_1910=n_43 & nl_1906=nl_2095 & v_bool_140_794'<=0 & 
  v_bool_136_795'<=0 & n_43<=-1 & v_boolean_143_793'<=0 & x!=null & 
  1<=bhl_2096 | l_1905=l_2094 & r_1909=r_2098 & flted_12_1902=0 & 
  flted_12_1901=0 & cl=1 & 1+nl_2095+nr_2099=n_43 & n=n_43 & 
  bhr_2100=bhl_2096 & bh=bhl_2096 & bh_45=bhl_2096 & bhr_1911=bhl_2096 & 
  S2_2101=S2_1912 & v_2093=v_1904 & S1_1908=S1_2097 & flted_12_1903=1 & 
  cl_44=1 & res=v_boolean_143_793' & bhl_1907=bhl_2096 & 1+nl_2095+
  nr_1910=n_43 & nl_1906=nl_2095 & v_bool_140_794'<=0 & v_bool_136_795'<=0 & 
  v_boolean_143_793'<=0 & x!=null & 1<=bhl_2096 & 1<=n_43) & S!=() & 
  S=union(S1_1908,S2_1912,{v_1904}) & S1=union(S1_2097,S2_2101,
  {v_2093})))))))))))))))))))))))))))))))))) --> BLACK1(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RED2(S2,S)
!!! POST:  S=S2
!!! PRE :  true
!!! REL :  RED1(S1,S)
!!! POST:  S=S1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RED1,RED2]
              EBase exists (Expl)(Impl)[n; cl; bh; 
                    S](ex)x::rb1<n,cl,bh,S>@M[Orig][LHSCase]@ rem br[{159,158,157}]&
                    (([true][1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::
                                
                                EXISTS(n_57,cl_58,bh_59,
                                S1: x::rb1<n_57,cl_58,bh_59,S1>@M[Orig][LHSCase]@ rem br[{158}]&
                                (
                                ([res][S1!=() & RED1(S1,S)][n=n_57 & 0!=n_57]
                                 [cl=cl_58 & cl=1][bh=bh_59 & 1<=bh_59]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(n_60,cl_61,bh_62,
                                   S2: x::rb1<n_60,cl_61,bh_62,S2>@M[Orig][LHSCase]@ rem br[{159,157}]&
                                   (
                                   ([!(res)][RED2(S2,S)][n=n_60]
                                    [cl=cl_61 & cl=0][bh=bh_62 & 1<=bh_62]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; cl; bh; 
                  S](ex)x::rb1<n,cl,bh,S>@M[Orig][LHSCase]@ rem br[{159,158,157}]&
                  (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::
                              
                              EXISTS(n_2692,cl_2693,bh_2694,
                              S1_2695: x::rb1<n_2692,cl_2693,bh_2694,S1_2695>@M[Orig][LHSCase]@ rem br[{158}]&
                              (
                              ([S=S1_2695 & S1_2695!=()][null!=x]
                               [bh=bh_2694 & 1<=bh]
                               [1=cl & 1=cl_2693 & 0<=cl & cl<=1]
                               [n=n_2692 & 0!=n_2692 & 0<=n][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n_2696,cl_2697,bh_2698,
                                 S2_2699: x::rb1<n_2696,cl_2697,bh_2698,S2_2699>@M[Orig][LHSCase]@ rem br[{159,157}]&
                                 (
                                 ([S=S2_2699][bh=bh_2698 & 1<=bh]
                                  [0=cl & 0=cl_2697 & 0<=cl & cl<=1]
                                  [n=n_2696 & 0<=n][!(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S2=S) --> RED2(S2,S),
 (S=S2 & S2=) --> RED2(S2,S),
 (exists(l_2370:exists(l_2469:exists(r_2375:exists(r_2474:exists(cl:exists(nr_2475:exists(n:exists(bh_62_2508:exists(bh_62:exists(bhl_2472:exists(bh:exists(bhl_2373:exists(flted_13_2368:exists(cl_61:exists(Anon_2471:exists(Anon_2476:exists(res:exists(bhr_2378:exists(nr_2376:exists(nl_2371:exists(nl_2470:exists(Anon_2372:exists(Anon_2377:exists(v_boolean_114_851':exists(v_bool_110_854':exists(x:exists(bhr_2477:exists(v_bool_113_853':exists(n_60:exists(S1_2473:exists(S2_2478:exists(v_2468:exists(S1_2374:exists(S2_2379:exists(v_2369:(l_2370=l_2469 & 
  r_2375=r_2474 & cl=0 & 1+nl_2470+nr_2475=n_60 & n=n_60 & S2_2478=S2_2379 & 
  v_2468=v_2369 & S1_2374=S1_2473 & -1+bh_62_2508=bhr_2477 & -1+
  bh_62=bhr_2477 & bhl_2472=bhr_2477 & -1+bh=bhr_2477 & bhl_2373=bhr_2477 & 
  flted_13_2368=0 & cl_61=0 & Anon_2471=Anon_2372 & Anon_2476=Anon_2377 & 
  res=v_boolean_114_851' & bhr_2378=bhr_2477 & 1+nl_2470+nr_2376=n_60 & 
  nl_2371=nl_2470 & 0<=Anon_2372 & Anon_2372<=1 & 0<=Anon_2377 & 
  Anon_2377<=1 & n_60<=-1 & v_boolean_114_851'<=0 & v_bool_110_854'<=0 & 
  x!=null & 1<=bhr_2477 & 1<=v_bool_113_853' | l_2370=l_2469 & 
  r_2375=r_2474 & cl=0 & 1+nl_2470+nr_2475=n_60 & n=n_60 & S2_2478=S2_2379 & 
  v_2468=v_2369 & S1_2374=S1_2473 & -1+bh_62_2508=bhr_2477 & -1+
  bh_62=bhr_2477 & bhl_2472=bhr_2477 & -1+bh=bhr_2477 & bhl_2373=bhr_2477 & 
  flted_13_2368=0 & cl_61=0 & Anon_2471=Anon_2372 & Anon_2476=Anon_2377 & 
  res=v_boolean_114_851' & bhr_2378=bhr_2477 & 1+nl_2470+nr_2376=n_60 & 
  nl_2371=nl_2470 & 0<=Anon_2372 & Anon_2372<=1 & 0<=Anon_2377 & 
  Anon_2377<=1 & v_boolean_114_851'<=0 & v_bool_110_854'<=0 & x!=null & 
  1<=bhr_2477 & 1<=v_bool_113_853' & 1<=n_60) & S2=union(S1_2473,S2_2478,
  {v_2468}) & S!=() & S=union(S1_2374,S2_2379,
  {v_2369}))))))))))))))))))))))))))))))))))))) --> RED2(S2,S),
 (exists(l_2347:exists(l_2536:exists(r_2351:exists(r_2540:exists(flted_12_2344:exists(flted_12_2343:exists(cl:exists(nr_2541:exists(n:exists(bhr_2542:exists(bh:exists(bh_59:exists(bhr_2353:exists(flted_12_2345:exists(cl_58:exists(bhl_2349:exists(res:exists(nr_2352:exists(nl_2348:exists(nl_2537:exists(v_bool_110_854':exists(v_bool_113_853':exists(x:exists(bhl_2538:exists(v_boolean_116_852':exists(n_57:exists(S1_2350:exists(S2_2354:exists(v_2346:exists(S1_2539:exists(S2_2543:exists(v_2535:(l_2347=l_2536 & 
  r_2351=r_2540 & flted_12_2344=0 & flted_12_2343=0 & cl=1 & 1+nl_2537+
  nr_2541=n_57 & n=n_57 & bhr_2542=bhl_2538 & bh=bhl_2538 & bh_59=bhl_2538 & 
  bhr_2353=bhl_2538 & S2_2543=S2_2354 & v_2535=v_2346 & S1_2350=S1_2539 & 
  flted_12_2345=1 & cl_58=1 & bhl_2349=bhl_2538 & res=v_boolean_116_852' & 1+
  nl_2537+nr_2352=n_57 & nl_2348=nl_2537 & v_bool_110_854'<=0 & 
  v_bool_113_853'<=0 & n_57<=-1 & x!=null & 1<=bhl_2538 & 
  1<=v_boolean_116_852' | l_2347=l_2536 & r_2351=r_2540 & flted_12_2344=0 & 
  flted_12_2343=0 & cl=1 & 1+nl_2537+nr_2541=n_57 & n=n_57 & 
  bhr_2542=bhl_2538 & bh=bhl_2538 & bh_59=bhl_2538 & bhr_2353=bhl_2538 & 
  S2_2543=S2_2354 & v_2535=v_2346 & S1_2350=S1_2539 & flted_12_2345=1 & 
  cl_58=1 & bhl_2349=bhl_2538 & res=v_boolean_116_852' & 1+nl_2537+
  nr_2352=n_57 & nl_2348=nl_2537 & v_bool_110_854'<=0 & v_bool_113_853'<=0 & 
  x!=null & 1<=bhl_2538 & 1<=v_boolean_116_852' & 1<=n_57) & S!=() & 
  S=union(S1_2350,S2_2354,{v_2346}) & S1=union(S1_2539,S2_2543,
  {v_2535})))))))))))))))))))))))))))))))))) --> RED1(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_red$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  ROT3(S4,S1,S2,S3)
!!! POST:  S1!=() & S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT3]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; bha; 
                    S3](ex)EXISTS(bha_188,bha_189,flted_20_185,flted_20_186,
                    flted_20_187: a::rb1<na,flted_20_187,bha,S1>@M[Orig][LHSCase]@ rem br[{158}] * 
                    b::rb1<nb,flted_20_186,bha_188,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    c::rb1<nc,flted_20_185,bha_189,S3>@M[Orig][LHSCase]@ rem br[{159,157}]&
                    (
                    ([flted_20_187=1][flted_20_186=0][flted_20_185=0]
                     [bha=bha_189 & bha=bha_188 & 1<=bha_189][null!=a][
                     0!=na][S1!=()]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(flted_21_182,flted_21_183,
                                flted_21_184,
                                S4: res::rb1<flted_21_184,flted_21_183,flted_21_182,S4>@M[Orig][LHSCase]@ rem br[{157}]&
                                (
                                ([flted_21_184=2+na+nb+nc][flted_21_183=0]
                                 [1!=flted_21_182 & -1+flted_21_182=bha]
                                 [S4!=() & ROT3(S4,S1,S2,S3)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; bha; 
                  S3](ex)a::rb1<na,flted_20_187,bha,S1>@M[Orig][LHSCase]@ rem br[{158}] * 
                  b::rb1<nb,flted_20_186,bha_188,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  c::rb1<nc,flted_20_185,bha_189,S3>@M[Orig][LHSCase]@ rem br[{159,157}]&
                  (
                  ([S1!=()]
                   [bha_188=bha & bha_189=bha & flted_20_185=0 & 
                     flted_20_186=0 & flted_20_187=1 & (na+1)<=0 & a!=null & 
                     1<=bha | bha_188=bha & bha_189=bha & flted_20_185=0 & 
                     flted_20_186=0 & flted_20_187=1 & a!=null & 1<=bha & 
                     1<=na]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(flted_21_2914,flted_21_2915,
                              flted_21_2916,
                              S4_2917: res::rb1<flted_21_2916,flted_21_2915,flted_21_2914,S4_2917>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S4_2917!=() & S1!=() & S4_2917=union(S1,S2,
                                 S3,{0},{0})]
                               [null!=res]
                               [1!=flted_21_2914 & 1<=bha & -1+
                                 flted_21_2914=bha]
                               [0=flted_21_2915]
                               [flted_21_2916=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=bha_189]
                               [0<=flted_20_185 & flted_20_185<=1]
                               [1<=bha_188]
                               [0<=flted_20_186 & flted_20_186<=1]
                               [0<=flted_20_187 & flted_20_187<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_21_183:exists(v_int_28_2749:exists(bhr_2759:exists(bha:exists(flted_21_182:exists(bhl_2754:exists(flted_20_2743:exists(flted_20_2744:exists(Anon_2753:exists(flted_20_2745:exists(v_int_26_2747:exists(v_2781:exists(v_int_26_2746:exists(v_int_28_2748:exists(S2_2789:exists(S1_2785:exists(c:exists(r_2786:exists(b:exists(l_2782:exists(nr_2757:exists(na:exists(Anon_2758:exists(r_2756:exists(res:exists(nb:exists(nc:exists(flted_21_184:exists(nl_2783:exists(nr_2787:exists(bhl_2784:exists(l_2751:exists(tmp_190':exists(v_node_28_1184':exists(nl_2752:exists(bhr_2788:exists(a:exists(S1_2755:exists(S2_2760:exists(v_2750:S2_2760=union(S1_2785,
  S2_2789,{v_2781}) & (flted_21_183=0 & v_int_28_2749=0 & 
  bhr_2759=bhr_2788 & bha=bhr_2788 & -1+flted_21_182=bhr_2788 & 
  bhl_2754=bhr_2788 & flted_20_2743=0 & flted_20_2744=0 & Anon_2753=1 & 
  flted_20_2745=1 & v_int_26_2747=1 & v_2781=0 & v_2750=0 & 
  v_int_26_2746=0 & v_int_28_2748=0 & S1=S1_2755 & S2_2789=S3 & S1_2785=S2 & 
  c=r_2786 & b=l_2782 & nr_2757=1+nl_2783+nr_2787 & na=nl_2752 & 
  Anon_2758=1 & r_2756=tmp_190' & res=v_node_28_1184' & nb=nl_2783 & 
  nc=nr_2787 & flted_21_184=2+nl_2752+nl_2783+nr_2787 & bhl_2784=bhr_2788 & 
  l_2751=a & nl_2752<=-1 & tmp_190'!=null & v_node_28_1184'!=null & 
  1<=bhr_2788 & a!=null | flted_21_183=0 & v_int_28_2749=0 & 
  bhr_2759=bhr_2788 & bha=bhr_2788 & -1+flted_21_182=bhr_2788 & 
  bhl_2754=bhr_2788 & flted_20_2743=0 & flted_20_2744=0 & Anon_2753=1 & 
  flted_20_2745=1 & v_int_26_2747=1 & v_2781=0 & v_2750=0 & 
  v_int_26_2746=0 & v_int_28_2748=0 & S1=S1_2755 & S2_2789=S3 & S1_2785=S2 & 
  c=r_2786 & b=l_2782 & nr_2757=1+nl_2783+nr_2787 & na=nl_2752 & 
  Anon_2758=1 & r_2756=tmp_190' & res=v_node_28_1184' & nb=nl_2783 & 
  nc=nr_2787 & flted_21_184=2+nl_2752+nl_2783+nr_2787 & bhl_2784=bhr_2788 & 
  l_2751=a & tmp_190'!=null & v_node_28_1184'!=null & 1<=nl_2752 & 
  1<=bhr_2788 & a!=null) & S1!=() & S4=union(S1_2755,S2_2760,
  {v_2750})))))))))))))))))))))))))))))))))))))))))) --> ROT3(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! REL :  ROT3R(S4,S1,S2,S3)
!!! POST:  S3!=() & S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT3R]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; bha; 
                    S3](ex)EXISTS(bha_124,bha_125,flted_62_121,flted_62_122,
                    flted_62_123: a::rb1<na,flted_62_123,bha,S1>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    b::rb1<nb,flted_62_122,bha_124,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                    c::rb1<nc,flted_62_121,bha_125,S3>@M[Orig][LHSCase]@ rem br[{158}]&
                    (
                    ([flted_62_123=0][flted_62_122=0][flted_62_121=1]
                     [bha=bha_125 & bha=bha_124 & 1<=bha_125][null!=c][
                     0!=nc][S3!=()]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::
                                EXISTS(flted_63_118,flted_63_119,
                                flted_63_120,
                                S4: res::rb1<flted_63_120,flted_63_119,flted_63_118,S4>@M[Orig][LHSCase]@ rem br[{157}]&
                                (
                                ([flted_63_120=2+na+nb+nc][flted_63_119=0]
                                 [1!=flted_63_118 & -1+flted_63_118=bha]
                                 [S4!=() & ROT3R(S4,S1,S2,S3)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; bha; 
                  S3](ex)a::rb1<na,flted_62_123,bha,S1>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  b::rb1<nb,flted_62_122,bha_124,S2>@M[Orig][LHSCase]@ rem br[{159,157}] * 
                  c::rb1<nc,flted_62_121,bha_125,S3>@M[Orig][LHSCase]@ rem br[{158}]&
                  (
                  ([S3!=()]
                   [bha_124=bha & bha_125=bha & flted_62_121=1 & 
                     flted_62_122=0 & flted_62_123=0 & (nc+1)<=0 & c!=null & 
                     1<=bha | bha_124=bha & bha_125=bha & flted_62_121=1 & 
                     flted_62_122=0 & flted_62_123=0 & c!=null & 1<=bha & 
                     1<=nc]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::
                              EXISTS(flted_63_3132,flted_63_3133,
                              flted_63_3134,
                              S4_3135: res::rb1<flted_63_3134,flted_63_3133,flted_63_3132,S4_3135>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S4_3135!=() & S3!=() & S4_3135=union(S1,S2,
                                 {0},S3,{0})]
                               [null!=res]
                               [1!=flted_63_3132 & 1<=bha & -1+
                                 flted_63_3132=bha]
                               [0=flted_63_3133]
                               [flted_63_3134=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=bha_125]
                               [0<=flted_62_121 & flted_62_121<=1]
                               [1<=bha_124]
                               [0<=flted_62_122 & flted_62_122<=1]
                               [0<=flted_62_123 & flted_62_123<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_63_119:exists(v_int_70_2967:exists(bhr_2977:exists(bha:exists(flted_63_118:exists(bhl_2972:exists(Anon_2976:exists(flted_62_2961:exists(flted_62_2962:exists(flted_62_2963:exists(v_int_68_2965:exists(v_2999:exists(v_int_68_2964:exists(v_int_70_2966:exists(S2_3007:exists(S1_3003:exists(b:exists(r_3004:exists(a:exists(l_3000:exists(nl_2970:exists(nc:exists(Anon_2971:exists(l_2969:exists(res:exists(na:exists(nb:exists(flted_63_120:exists(nl_3001:exists(nr_3005:exists(bhr_3006:exists(r_2974:exists(tmp_126':exists(v_node_70_1019':exists(nr_2975:exists(bhl_3002:exists(c:exists(S1_2973:exists(S2_2978:exists(v_2968:S1_2973=union(S1_3003,
  S2_3007,{v_2999}) & (flted_63_119=0 & v_int_70_2967=0 & 
  bhr_2977=bhl_3002 & bha=bhl_3002 & -1+flted_63_118=bhl_3002 & 
  bhl_2972=bhl_3002 & Anon_2976=1 & flted_62_2961=1 & flted_62_2962=0 & 
  flted_62_2963=0 & v_int_68_2965=1 & v_2999=0 & v_2968=0 & 
  v_int_68_2964=0 & v_int_70_2966=0 & S3=S2_2978 & S2_3007=S2 & S1_3003=S1 & 
  b=r_3004 & a=l_3000 & nl_2970=1+nl_3001+nr_3005 & nc=nr_2975 & 
  Anon_2971=1 & l_2969=tmp_126' & res=v_node_70_1019' & na=nl_3001 & 
  nb=nr_3005 & flted_63_120=2+nl_3001+nr_2975+nr_3005 & bhr_3006=bhl_3002 & 
  r_2974=c & nr_2975<=-1 & tmp_126'!=null & v_node_70_1019'!=null & 
  1<=bhl_3002 & c!=null | flted_63_119=0 & v_int_70_2967=0 & 
  bhr_2977=bhl_3002 & bha=bhl_3002 & -1+flted_63_118=bhl_3002 & 
  bhl_2972=bhl_3002 & Anon_2976=1 & flted_62_2961=1 & flted_62_2962=0 & 
  flted_62_2963=0 & v_int_68_2965=1 & v_2999=0 & v_2968=0 & 
  v_int_68_2964=0 & v_int_70_2966=0 & S3=S2_2978 & S2_3007=S2 & S1_3003=S1 & 
  b=r_3004 & a=l_3000 & nl_2970=1+nl_3001+nr_3005 & nc=nr_2975 & 
  Anon_2971=1 & l_2969=tmp_126' & res=v_node_70_1019' & na=nl_3001 & 
  nb=nr_3005 & flted_63_120=2+nl_3001+nr_2975+nr_3005 & bhr_3006=bhl_3002 & 
  r_2974=c & tmp_126'!=null & v_node_70_1019'!=null & 1<=nr_2975 & 
  1<=bhl_3002 & c!=null) & S3!=() & S4=union(S1_2973,S2_2978,
  {v_2968})))))))))))))))))))))))))))))))))))))))))) --> ROT3R(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 6.3 second(s)
	Time spent in main process: 0.69 second(s)
	Time spent in child processes: 5.61 second(s)
