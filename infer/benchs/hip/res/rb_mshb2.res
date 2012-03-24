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
                              EXISTS(flted_43_1632,flted_43_1633,
                              flted_43_1634,
                              S5_1635: res::rb1<flted_43_1634,flted_43_1633,flted_43_1632,S5_1635>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S5_1635!=() & S5_1635=union(S1,S2,{0},S3,S4,
                                 {0},{0})]
                               [null!=res]
                               [1!=flted_43_1632 & 1<=bha & -1+
                                 flted_43_1632=bha]
                               [0=flted_43_1633]
                               [flted_43_1634=3+na+nb+nc+nd & 0<=na & 
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
                              EXISTS(flted_83_1784,flted_83_1785,
                              flted_83_1786,
                              S5_1787: res::rb1<flted_83_1786,flted_83_1785,flted_83_1784,S5_1787>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S5_1787!=() & S5_1787=union(S1,S2,S3,S4,{0},
                                 {0},{0})]
                               [null!=res]
                               [1!=flted_83_1784 & 1<=bha & -1+
                                 flted_83_1784=bha]
                               [0=flted_83_1785]
                               [flted_83_1786=3+na+nb+nc+nd & 0<=na & 
                                 0<=nd & 0<=nb & 0<=nc]
                               [1<=bha_96][0<=flted_82_90 & flted_82_90<=1]
                               [1<=bha_95][0<=flted_82_91 & flted_82_91<=1]
                               [1<=bha_94][0<=flted_82_92 & flted_82_92<=1]
                               [0<=flted_82_93 & flted_82_93<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S3_1662:exists(v_1689:exists(S4_1766:exists(S1_1657:exists(S2_1659:exists(S2_1697:exists(S1_1693:v_1689=0 & 
  S4_1766=union(S1_1657,S2_1659,S3_1662,{0},{0}) & S3_1662=union(S1_1693,
  S2_1697,{v_1689}) & S4_1766=S5 & S1=S1_1657 & S2_1659=S2 & S4=S2_1697 & 
  S3=S1_1693)))))))) --> ROT2R(S5,S1,S2,S3,S4)]
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
!!! POST:  S1=S
!!! PRE :  true
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
                              
                              EXISTS(n_2202,cl_2203,bh_2204,
                              S1_2205: x::rb1<n_2202,cl_2203,bh_2204,S1_2205>@M[Orig][LHSCase]@ rem br[{158}]&
                              (
                              ([S=S1_2205 & S1_2205!=()][null!=x]
                               [bh=bh_2204 & 1<=bh]
                               [1=cl & 1=cl_2203 & 0<=cl & cl<=1]
                               [n=n_2202 & 0!=n_2202 & 0<=n][!(res)]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n_2206,cl_2207,bh_2208,
                                 S2_2209: x::rb1<n_2206,cl_2207,bh_2208,S2_2209>@M[Orig][LHSCase]@ rem br[{159,157}]&
                                 (
                                 ([S=S2_2209][bh=bh_2208 & 1<=bh]
                                  [0=cl & 0=cl_2207 & 0<=cl & cl<=1]
                                  [n=n_2206 & 0<=n][res]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S2=S) --> BLACK2(S2,S),
 (S=S2 & S2=) --> BLACK2(S2,S),
 (exists(l_1900:exists(l_1999:exists(r_1905:exists(r_2004:exists(cl:exists(nr_2005:exists(n:exists(bh_48_2038:exists(bh_48:exists(bhl_2002:exists(bh:exists(bhl_1903:exists(flted_13_1898:exists(cl_47:exists(Anon_2001:exists(Anon_2006:exists(bhr_1908:exists(res:exists(nr_1906:exists(nl_1901:exists(nl_2000:exists(Anon_1902:exists(Anon_1907:exists(v_bool_136_795':exists(x:exists(bhr_2007:exists(v_boolean_141_792':exists(v_bool_140_794':exists(n_46:exists(S1_2003:exists(S2_2008:exists(v_1998:exists(S1_1904:exists(S2_1909:exists(v_1899:(l_1900=l_1999 & 
  r_1905=r_2004 & cl=0 & 1+nl_2000+nr_2005=n_46 & n=n_46 & S2_2008=S2_1909 & 
  v_1998=v_1899 & S1_1904=S1_2003 & -1+bh_48_2038=bhr_2007 & -1+
  bh_48=bhr_2007 & bhl_2002=bhr_2007 & -1+bh=bhr_2007 & bhl_1903=bhr_2007 & 
  flted_13_1898=0 & cl_47=0 & Anon_2001=Anon_1902 & Anon_2006=Anon_1907 & 
  bhr_1908=bhr_2007 & res=v_boolean_141_792' & 1+nl_2000+nr_1906=n_46 & 
  nl_1901=nl_2000 & 0<=Anon_1902 & Anon_1902<=1 & 0<=Anon_1907 & 
  Anon_1907<=1 & n_46<=-1 & v_bool_136_795'<=0 & x!=null & 1<=bhr_2007 & 
  1<=v_boolean_141_792' & 1<=v_bool_140_794' | l_1900=l_1999 & 
  r_1905=r_2004 & cl=0 & 1+nl_2000+nr_2005=n_46 & n=n_46 & S2_2008=S2_1909 & 
  v_1998=v_1899 & S1_1904=S1_2003 & -1+bh_48_2038=bhr_2007 & -1+
  bh_48=bhr_2007 & bhl_2002=bhr_2007 & -1+bh=bhr_2007 & bhl_1903=bhr_2007 & 
  flted_13_1898=0 & cl_47=0 & Anon_2001=Anon_1902 & Anon_2006=Anon_1907 & 
  bhr_1908=bhr_2007 & res=v_boolean_141_792' & 1+nl_2000+nr_1906=n_46 & 
  nl_1901=nl_2000 & 0<=Anon_1902 & Anon_1902<=1 & 0<=Anon_1907 & 
  Anon_1907<=1 & v_bool_136_795'<=0 & x!=null & 1<=bhr_2007 & 
  1<=v_boolean_141_792' & 1<=v_bool_140_794' & 1<=n_46) & S2=union(S1_2003,
  S2_2008,{v_1998}) & S!=() & S=union(S1_1904,S2_1909,
  {v_1899}))))))))))))))))))))))))))))))))))))) --> BLACK2(S2,S),
 (exists(l_1877:exists(l_2053:exists(r_1881:exists(r_2057:exists(flted_12_1874:exists(flted_12_1873:exists(cl:exists(nr_2058:exists(n:exists(bhr_2059:exists(bh:exists(bh_45:exists(bhr_1883:exists(flted_12_1875:exists(cl_44:exists(res:exists(bhl_1879:exists(nr_1882:exists(nl_1878:exists(nl_2054:exists(v_bool_140_794':exists(v_bool_136_795':exists(v_boolean_143_793':exists(x:exists(bhl_2055:exists(n_43:exists(S1_1880:exists(S2_1884:exists(v_1876:exists(S1_2056:exists(S2_2060:exists(v_2052:(l_1877=l_2053 & 
  r_1881=r_2057 & flted_12_1874=0 & flted_12_1873=0 & cl=1 & 1+nl_2054+
  nr_2058=n_43 & n=n_43 & bhr_2059=bhl_2055 & bh=bhl_2055 & bh_45=bhl_2055 & 
  bhr_1883=bhl_2055 & S2_2060=S2_1884 & v_2052=v_1876 & S1_1880=S1_2056 & 
  flted_12_1875=1 & cl_44=1 & res=v_boolean_143_793' & bhl_1879=bhl_2055 & 1+
  nl_2054+nr_1882=n_43 & nl_1878=nl_2054 & v_bool_140_794'<=0 & 
  v_bool_136_795'<=0 & n_43<=-1 & v_boolean_143_793'<=0 & x!=null & 
  1<=bhl_2055 | l_1877=l_2053 & r_1881=r_2057 & flted_12_1874=0 & 
  flted_12_1873=0 & cl=1 & 1+nl_2054+nr_2058=n_43 & n=n_43 & 
  bhr_2059=bhl_2055 & bh=bhl_2055 & bh_45=bhl_2055 & bhr_1883=bhl_2055 & 
  S2_2060=S2_1884 & v_2052=v_1876 & S1_1880=S1_2056 & flted_12_1875=1 & 
  cl_44=1 & res=v_boolean_143_793' & bhl_1879=bhl_2055 & 1+nl_2054+
  nr_1882=n_43 & nl_1878=nl_2054 & v_bool_140_794'<=0 & v_bool_136_795'<=0 & 
  v_boolean_143_793'<=0 & x!=null & 1<=bhl_2055 & 1<=n_43) & S!=() & 
  S=union(S1_1880,S2_1884,{v_1876}) & S1=union(S1_2056,S2_2060,
  {v_2052})))))))))))))))))))))))))))))))))) --> BLACK1(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RED2(S2,S)
!!! POST:  S=S2
!!! PRE :  true
!!! REL :  RED1(S1,S)
!!! POST:  S1=S
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
                              
                              EXISTS(n_2624,cl_2625,bh_2626,
                              S1_2627: x::rb1<n_2624,cl_2625,bh_2626,S1_2627>@M[Orig][LHSCase]@ rem br[{158}]&
                              (
                              ([S=S1_2627 & S1_2627!=()][null!=x]
                               [bh=bh_2626 & 1<=bh]
                               [1=cl & 1=cl_2625 & 0<=cl & cl<=1]
                               [n=n_2624 & 0!=n_2624 & 0<=n][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n_2628,cl_2629,bh_2630,
                                 S2_2631: x::rb1<n_2628,cl_2629,bh_2630,S2_2631>@M[Orig][LHSCase]@ rem br[{159,157}]&
                                 (
                                 ([S=S2_2631][bh=bh_2630 & 1<=bh]
                                  [0=cl & 0=cl_2629 & 0<=cl & cl<=1]
                                  [n=n_2628 & 0<=n][!(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S2=S) --> RED2(S2,S),
 (S=S2 & S2=) --> RED2(S2,S),
 (exists(l_2322:exists(l_2421:exists(r_2327:exists(r_2426:exists(cl:exists(nr_2427:exists(n:exists(bh_62_2460:exists(bh_62:exists(bhl_2424:exists(bh:exists(bhl_2325:exists(flted_13_2320:exists(cl_61:exists(Anon_2423:exists(Anon_2428:exists(res:exists(bhr_2330:exists(nr_2328:exists(nl_2323:exists(nl_2422:exists(Anon_2324:exists(Anon_2329:exists(v_boolean_114_851':exists(v_bool_110_854':exists(x:exists(bhr_2429:exists(v_bool_113_853':exists(n_60:exists(S1_2425:exists(S2_2430:exists(v_2420:exists(S1_2326:exists(S2_2331:exists(v_2321:(l_2322=l_2421 & 
  r_2327=r_2426 & cl=0 & 1+nl_2422+nr_2427=n_60 & n=n_60 & S2_2430=S2_2331 & 
  v_2420=v_2321 & S1_2326=S1_2425 & -1+bh_62_2460=bhr_2429 & -1+
  bh_62=bhr_2429 & bhl_2424=bhr_2429 & -1+bh=bhr_2429 & bhl_2325=bhr_2429 & 
  flted_13_2320=0 & cl_61=0 & Anon_2423=Anon_2324 & Anon_2428=Anon_2329 & 
  res=v_boolean_114_851' & bhr_2330=bhr_2429 & 1+nl_2422+nr_2328=n_60 & 
  nl_2323=nl_2422 & 0<=Anon_2324 & Anon_2324<=1 & 0<=Anon_2329 & 
  Anon_2329<=1 & n_60<=-1 & v_boolean_114_851'<=0 & v_bool_110_854'<=0 & 
  x!=null & 1<=bhr_2429 & 1<=v_bool_113_853' | l_2322=l_2421 & 
  r_2327=r_2426 & cl=0 & 1+nl_2422+nr_2427=n_60 & n=n_60 & S2_2430=S2_2331 & 
  v_2420=v_2321 & S1_2326=S1_2425 & -1+bh_62_2460=bhr_2429 & -1+
  bh_62=bhr_2429 & bhl_2424=bhr_2429 & -1+bh=bhr_2429 & bhl_2325=bhr_2429 & 
  flted_13_2320=0 & cl_61=0 & Anon_2423=Anon_2324 & Anon_2428=Anon_2329 & 
  res=v_boolean_114_851' & bhr_2330=bhr_2429 & 1+nl_2422+nr_2328=n_60 & 
  nl_2323=nl_2422 & 0<=Anon_2324 & Anon_2324<=1 & 0<=Anon_2329 & 
  Anon_2329<=1 & v_boolean_114_851'<=0 & v_bool_110_854'<=0 & x!=null & 
  1<=bhr_2429 & 1<=v_bool_113_853' & 1<=n_60) & S2=union(S1_2425,S2_2430,
  {v_2420}) & S!=() & S=union(S1_2326,S2_2331,
  {v_2321}))))))))))))))))))))))))))))))))))))) --> RED2(S2,S),
 (exists(l_2299:exists(l_2475:exists(r_2303:exists(r_2479:exists(flted_12_2296:exists(flted_12_2295:exists(cl:exists(nr_2480:exists(n:exists(bhr_2481:exists(bh:exists(bh_59:exists(bhr_2305:exists(flted_12_2297:exists(cl_58:exists(bhl_2301:exists(res:exists(nr_2304:exists(nl_2300:exists(nl_2476:exists(v_bool_110_854':exists(v_bool_113_853':exists(x:exists(bhl_2477:exists(v_boolean_116_852':exists(n_57:exists(S1_2302:exists(S2_2306:exists(v_2298:exists(S1_2478:exists(S2_2482:exists(v_2474:(l_2299=l_2475 & 
  r_2303=r_2479 & flted_12_2296=0 & flted_12_2295=0 & cl=1 & 1+nl_2476+
  nr_2480=n_57 & n=n_57 & bhr_2481=bhl_2477 & bh=bhl_2477 & bh_59=bhl_2477 & 
  bhr_2305=bhl_2477 & S2_2482=S2_2306 & v_2474=v_2298 & S1_2302=S1_2478 & 
  flted_12_2297=1 & cl_58=1 & bhl_2301=bhl_2477 & res=v_boolean_116_852' & 1+
  nl_2476+nr_2304=n_57 & nl_2300=nl_2476 & v_bool_110_854'<=0 & 
  v_bool_113_853'<=0 & n_57<=-1 & x!=null & 1<=bhl_2477 & 
  1<=v_boolean_116_852' | l_2299=l_2475 & r_2303=r_2479 & flted_12_2296=0 & 
  flted_12_2295=0 & cl=1 & 1+nl_2476+nr_2480=n_57 & n=n_57 & 
  bhr_2481=bhl_2477 & bh=bhl_2477 & bh_59=bhl_2477 & bhr_2305=bhl_2477 & 
  S2_2482=S2_2306 & v_2474=v_2298 & S1_2302=S1_2478 & flted_12_2297=1 & 
  cl_58=1 & bhl_2301=bhl_2477 & res=v_boolean_116_852' & 1+nl_2476+
  nr_2304=n_57 & nl_2300=nl_2476 & v_bool_110_854'<=0 & v_bool_113_853'<=0 & 
  x!=null & 1<=bhl_2477 & 1<=v_boolean_116_852' & 1<=n_57) & S!=() & 
  S=union(S1_2302,S2_2306,{v_2298}) & S1=union(S1_2478,S2_2482,
  {v_2474})))))))))))))))))))))))))))))))))) --> RED1(S1,S)]
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
                              EXISTS(flted_21_2830,flted_21_2831,
                              flted_21_2832,
                              S4_2833: res::rb1<flted_21_2832,flted_21_2831,flted_21_2830,S4_2833>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S4_2833!=() & S1!=() & S4_2833=union(S1,S2,
                                 S3,{0},{0})]
                               [null!=res]
                               [1!=flted_21_2830 & 1<=bha & -1+
                                 flted_21_2830=bha]
                               [0=flted_21_2831]
                               [flted_21_2832=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=bha_189]
                               [0<=flted_20_185 & flted_20_185<=1]
                               [1<=bha_188]
                               [0<=flted_20_186 & flted_20_186<=1]
                               [0<=flted_20_187 & flted_20_187<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_21_183:exists(v_int_28_2681:exists(bhr_2691:exists(bha:exists(flted_21_182:exists(bhl_2686:exists(flted_20_2675:exists(flted_20_2676:exists(Anon_2685:exists(flted_20_2677:exists(v_int_26_2679:exists(v_2713:exists(v_int_26_2678:exists(v_int_28_2680:exists(S2_2721:exists(S1_2717:exists(c:exists(r_2718:exists(b:exists(l_2714:exists(nr_2689:exists(na:exists(Anon_2690:exists(r_2688:exists(res:exists(nb:exists(nc:exists(flted_21_184:exists(nl_2715:exists(nr_2719:exists(bhl_2716:exists(l_2683:exists(tmp_190':exists(v_node_28_1184':exists(nl_2684:exists(bhr_2720:exists(a:exists(S1_2687:exists(S2_2692:exists(v_2682:S2_2692=union(S1_2717,
  S2_2721,{v_2713}) & (flted_21_183=0 & v_int_28_2681=0 & 
  bhr_2691=bhr_2720 & bha=bhr_2720 & -1+flted_21_182=bhr_2720 & 
  bhl_2686=bhr_2720 & flted_20_2675=0 & flted_20_2676=0 & Anon_2685=1 & 
  flted_20_2677=1 & v_int_26_2679=1 & v_2713=0 & v_2682=0 & 
  v_int_26_2678=0 & v_int_28_2680=0 & S1=S1_2687 & S2_2721=S3 & S1_2717=S2 & 
  c=r_2718 & b=l_2714 & nr_2689=1+nl_2715+nr_2719 & na=nl_2684 & 
  Anon_2690=1 & r_2688=tmp_190' & res=v_node_28_1184' & nb=nl_2715 & 
  nc=nr_2719 & flted_21_184=2+nl_2684+nl_2715+nr_2719 & bhl_2716=bhr_2720 & 
  l_2683=a & nl_2684<=-1 & tmp_190'!=null & v_node_28_1184'!=null & 
  1<=bhr_2720 & a!=null | flted_21_183=0 & v_int_28_2681=0 & 
  bhr_2691=bhr_2720 & bha=bhr_2720 & -1+flted_21_182=bhr_2720 & 
  bhl_2686=bhr_2720 & flted_20_2675=0 & flted_20_2676=0 & Anon_2685=1 & 
  flted_20_2677=1 & v_int_26_2679=1 & v_2713=0 & v_2682=0 & 
  v_int_26_2678=0 & v_int_28_2680=0 & S1=S1_2687 & S2_2721=S3 & S1_2717=S2 & 
  c=r_2718 & b=l_2714 & nr_2689=1+nl_2715+nr_2719 & na=nl_2684 & 
  Anon_2690=1 & r_2688=tmp_190' & res=v_node_28_1184' & nb=nl_2715 & 
  nc=nr_2719 & flted_21_184=2+nl_2684+nl_2715+nr_2719 & bhl_2716=bhr_2720 & 
  l_2683=a & tmp_190'!=null & v_node_28_1184'!=null & 1<=nl_2684 & 
  1<=bhr_2720 & a!=null) & S1!=() & S4=union(S1_2687,S2_2692,
  {v_2682})))))))))))))))))))))))))))))))))))))))))) --> ROT3(S4,S1,S2,S3)]
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
                              EXISTS(flted_63_3032,flted_63_3033,
                              flted_63_3034,
                              S4_3035: res::rb1<flted_63_3034,flted_63_3033,flted_63_3032,S4_3035>@M[Orig][LHSCase]@ rem br[{157}]&
                              (
                              ([S4_3035!=() & S3!=() & S4_3035=union(S1,S2,
                                 {0},S3,{0})]
                               [null!=res]
                               [1!=flted_63_3032 & 1<=bha & -1+
                                 flted_63_3032=bha]
                               [0=flted_63_3033]
                               [flted_63_3034=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=bha_125]
                               [0<=flted_62_121 & flted_62_121<=1]
                               [1<=bha_124]
                               [0<=flted_62_122 & flted_62_122<=1]
                               [0<=flted_62_123 & flted_62_123<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_63_119:exists(v_int_70_2883:exists(bhr_2893:exists(bha:exists(flted_63_118:exists(bhl_2888:exists(Anon_2892:exists(flted_62_2877:exists(flted_62_2878:exists(flted_62_2879:exists(v_int_68_2881:exists(v_2915:exists(v_int_68_2880:exists(v_int_70_2882:exists(S2_2923:exists(S1_2919:exists(b:exists(r_2920:exists(a:exists(l_2916:exists(nl_2886:exists(nc:exists(Anon_2887:exists(l_2885:exists(res:exists(na:exists(nb:exists(flted_63_120:exists(nl_2917:exists(nr_2921:exists(bhr_2922:exists(r_2890:exists(tmp_126':exists(v_node_70_1019':exists(nr_2891:exists(bhl_2918:exists(c:exists(S1_2889:exists(S2_2894:exists(v_2884:S1_2889=union(S1_2919,
  S2_2923,{v_2915}) & (flted_63_119=0 & v_int_70_2883=0 & 
  bhr_2893=bhl_2918 & bha=bhl_2918 & -1+flted_63_118=bhl_2918 & 
  bhl_2888=bhl_2918 & Anon_2892=1 & flted_62_2877=1 & flted_62_2878=0 & 
  flted_62_2879=0 & v_int_68_2881=1 & v_2915=0 & v_2884=0 & 
  v_int_68_2880=0 & v_int_70_2882=0 & S3=S2_2894 & S2_2923=S2 & S1_2919=S1 & 
  b=r_2920 & a=l_2916 & nl_2886=1+nl_2917+nr_2921 & nc=nr_2891 & 
  Anon_2887=1 & l_2885=tmp_126' & res=v_node_70_1019' & na=nl_2917 & 
  nb=nr_2921 & flted_63_120=2+nl_2917+nr_2891+nr_2921 & bhr_2922=bhl_2918 & 
  r_2890=c & nr_2891<=-1 & tmp_126'!=null & v_node_70_1019'!=null & 
  1<=bhl_2918 & c!=null | flted_63_119=0 & v_int_70_2883=0 & 
  bhr_2893=bhl_2918 & bha=bhl_2918 & -1+flted_63_118=bhl_2918 & 
  bhl_2888=bhl_2918 & Anon_2892=1 & flted_62_2877=1 & flted_62_2878=0 & 
  flted_62_2879=0 & v_int_68_2881=1 & v_2915=0 & v_2884=0 & 
  v_int_68_2880=0 & v_int_70_2882=0 & S3=S2_2894 & S2_2923=S2 & S1_2919=S1 & 
  b=r_2920 & a=l_2916 & nl_2886=1+nl_2917+nr_2921 & nc=nr_2891 & 
  Anon_2887=1 & l_2885=tmp_126' & res=v_node_70_1019' & na=nl_2917 & 
  nb=nr_2921 & flted_63_120=2+nl_2917+nr_2891+nr_2921 & bhr_2922=bhl_2918 & 
  r_2890=c & tmp_126'!=null & v_node_70_1019'!=null & 1<=nr_2891 & 
  1<=bhl_2918 & c!=null) & S3!=() & S4=union(S1_2889,S2_2894,
  {v_2884})))))))))))))))))))))))))))))))))))))))))) --> ROT3R(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 1.99 second(s)
	Time spent in main process: 0.56 second(s)
	Time spent in child processes: 1.43 second(s)
