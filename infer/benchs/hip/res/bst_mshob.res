/usr/local/bin/mona

Processing file "bst_mshob.ss"
Parsing bst_mshob.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure append$node2~node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[Anon_11; m; S1; Anon_12; n; 
                    S2](ex)x::dll<Anon_11,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                    y::dll<Anon_12,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(flted_29_111,r,
                                S: res::dll<r,flted_29_111,S>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([flted_29_111=m+n][APP(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_11; m; S1; Anon_12; n; 
                  S2](ex)x::dll<Anon_11,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                  y::dll<Anon_12,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(flted_29_1375,r_1376,
                              S_1377: res::dll<r_1376,flted_29_1375,S_1377>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([S_1377=union(S1,S2)]
                               [flted_29_1375=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1338:exists(v_1140:exists(v_1335:exists(S1_1143:S1!=() & 
  S1=union(S1_1143,{v_1140}) & S=union(S1_1338,{v_1335}) & 
  APP(S_1193,S1_1149,S2_1152) & S2_1152=S2 & S1_1338=S_1193 & 
  v_1140=v_1335 & S1_1143=S1_1149 & S_1193=))))) --> APP(S,S1,S2),
 (S=S2 & S1=) --> APP(S,S1,S2),
 (exists(S1_1254:exists(v_1251:exists(S1_1284:exists(v_1281:exists(S1_1271:exists(v_1268:exists(S1_1143:exists(v_1140:S1_1254=S1_1284 & 
  v_1251=v_1281 & S_1193=union(S1_1254,{v_1251}) & S_1193!=() & 
  S1_1271=union(S1_1284,{v_1281}) & S1_1143=S1_1149 & v_1140=v_1268 & 
  S2_1152=S2 & APP(S_1193,S1_1149,S2_1152) & S=union(S1_1271,{v_1268}) & 
  S1=union(S1_1143,{v_1140}) & S1!=()))))))))) --> APP(S,S1,S2),
 (exists(S1_1338:exists(v_1335:exists(S1_1143:exists(v_1140:S_1193= & 
  S1_1143=S1_1149 & v_1140=v_1335 & S1_1338=S_1193 & S2_1152=S2 & 
  APP(S_1193,S1_1149,S2_1152) & S=union(S1_1338,{v_1335}) & S1=union(S1_1143,
  {v_1140}) & S1!=()))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure appendC$node2~node2... 
!!! REL :  C(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_54_106,Anon_15,
                                S: res::dll<Anon_15,flted_54_106,S>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([flted_54_106=m+n][C(S,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(flted_54_1642,Anon_1643,
                              S_1644: res::dll<Anon_1643,flted_54_1642,S_1644>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([S_1644=union(S1,S2)]
                               [flted_54_1642=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=S2 & S1=) --> C(S,S1,S2),
 (exists(S1_1530:exists(v_1527:exists(S1_1564:exists(v_1561:exists(S1_1551:exists(v_1548:exists(S1_1420:exists(v_1417:S1_1530=S1_1564 & 
  v_1527=v_1561 & S_1477=union(S1_1530,{v_1527}) & S_1477!=() & 
  S1_1551=union(S1_1564,{v_1561}) & S1_1420=S1_1426 & v_1417=v_1548 & 
  S2_1429=S2 & C(S_1477,S1_1426,S2_1429) & S=union(S1_1551,{v_1548}) & 
  S1!=() & S1=union(S1_1420,{v_1417})))))))))) --> C(S,S1,S2),
 (exists(S1_1618:exists(v_1615:exists(S1_1420:exists(v_1417:S_1469= & 
  S1_1618= & S1_1426=S1_1420 & v_1417=v_1615 & S2=S2_1429 & 
  C(S_1469,S1_1426,S2_1429) & S=union(S1_1618,{v_1615}) & S1!=() & 
  S1=union(S1_1420,{v_1417})))))) --> C(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appendC$node2~node2 SUCCESS

Checking procedure count$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure count$node2 SUCCESS

Checking procedure remove_min$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RMVM(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMVM]
              EBase exists (Expl)(Impl)[n; h; s; b; 
                    S1](ex)x::bst3<n,h,s,b,S1>@M[Orig][LHSCase]@ rem br[{287}]&
                    (([null!=x][s<=b][0!=n][0!=h][S1!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::ref [x]
                                EXISTS(b_87,flted_150_86,h1,s1,
                                S2: x'::bst3<flted_150_86,h1,s1,b_87,S2>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                (
                                ([1+flted_150_86=n][h1<=h]
                                 [b=b_87 & s1<=b_87 & res<=s1 & s<=res]
                                 [RMVM(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; s; b; 
                  S1](ex)x::bst3<n,h,s,b,S1>@M[Orig][LHSCase]@ rem br[{287}]&
                  (
                  ([S1!=()]
                   [(h+1)<=0 & (n+1)<=0 & s<=b & x!=null | (n+1)<=0 & s<=b & 
                     x!=null & 1<=h | (h+1)<=0 & s<=b & x!=null & 1<=n | 
                     s<=b & x!=null & 1<=h & 1<=n]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              EXISTS(b_2155,flted_150_2156,h1_2157,s1_2158,
                              S2_2159: x'::bst3<flted_150_2156,h1_2157,s1_2158,b_2155,S2_2159>@M[Orig][LHSCase]@ rem br[{288,287}]&
                              (
                              ([b=b_2155 & s1_2158<=b_2155 & s<=b & s<=res & 
                                 res<=s1_2158]
                               [h1_2157<=h & 0<=h][1+flted_150_2156=n & 0<=n]
                               [S2_2159<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(x':exists(q_1849:exists(res:exists(n1_1846:exists(n:exists(h1_1847:exists(h:exists(sm_1840:exists(v_int_159_765':exists(s1:exists(b:exists(flted_150_86:exists(h1:exists(s:exists(pl_1842:exists(tmp_88':exists(qs_1843:exists(lg_1841:exists(p_1845:exists(x:exists(n2_1850:exists(v_bool_154_767':exists(h2_1851:exists(S2_1852:exists(v_1844:exists(S1_1848:(x'=q_1849 & 
  S2=S2_1852 & res=tmp_88' & v_1844=tmp_88' & n1_1846=0 & -1+n=n2_1850 & 
  h1_1847=0 & h=1 & sm_1840=s & v_int_159_765'=tmp_88' & s1=qs_1843 & 
  b=lg_1841 & flted_150_86=n2_1850 & h1=h2_1851 & s<=pl_1842 & 
  pl_1842<=tmp_88' & tmp_88'<=qs_1843 & qs_1843<=lg_1841 & h2_1851<=0 & 
  p_1845=null & n2_1850<=-2 & x!=null & 1<=v_bool_154_767' | x'=q_1849 & 
  S2=S2_1852 & res=tmp_88' & v_1844=tmp_88' & n1_1846=0 & -1+n=n2_1850 & 
  h1_1847=0 & h=1 & sm_1840=s & v_int_159_765'=tmp_88' & s1=qs_1843 & 
  b=lg_1841 & flted_150_86=n2_1850 & h1=h2_1851 & s<=pl_1842 & 
  pl_1842<=tmp_88' & tmp_88'<=qs_1843 & qs_1843<=lg_1841 & h2_1851<=0 & 
  p_1845=null & x!=null & 0<=n2_1850 & 1<=v_bool_154_767' | x'=q_1849 & 
  S2=S2_1852 & res=tmp_88' & v_1844=tmp_88' & n1_1846=0 & -1+n=n2_1850 & 
  h1_1847=0 & -1+h=h2_1851 & sm_1840=s & v_int_159_765'=tmp_88' & 
  s1=qs_1843 & b=lg_1841 & flted_150_86=n2_1850 & h1=h2_1851 & s<=pl_1842 & 
  pl_1842<=tmp_88' & tmp_88'<=qs_1843 & qs_1843<=lg_1841 & p_1845=null & 
  n2_1850<=-2 & x!=null & 1<=v_bool_154_767' & 1<=h2_1851 | x'=q_1849 & 
  S2=S2_1852 & res=tmp_88' & v_1844=tmp_88' & n1_1846=0 & -1+n=n2_1850 & 
  h1_1847=0 & -1+h=h2_1851 & sm_1840=s & v_int_159_765'=tmp_88' & 
  s1=qs_1843 & b=lg_1841 & flted_150_86=n2_1850 & h1=h2_1851 & s<=pl_1842 & 
  pl_1842<=tmp_88' & tmp_88'<=qs_1843 & qs_1843<=lg_1841 & p_1845=null & 
  x!=null & 0<=n2_1850 & 1<=v_bool_154_767' & 1<=h2_1851) & S1=union(S1_1848,
  S2_1852,{v_1844}) & S1!=() & 
  S1_1848=))))))))))))))))))))))))))) --> RMVM(S1,S2),
 (exists(p_1965:exists(xleft_1963:exists(q_1969:exists(q_1849:exists(h2_1971:exists(h1:exists(h1_1960:exists(h_1889:exists(h1_1847:exists(n1_1966:exists(n2_1970:exists(n1_1846:exists(n:exists(flted_150_1959:exists(n_1888:exists(res:exists(s:exists(b:exists(lg_1841:exists(tmp_90':exists(s1_1961:exists(s_1890:exists(b_1891:exists(x':exists(sm_1840:exists(v_int_166_766':exists(s1:exists(pl_1842:exists(qs_1843:exists(b_87:exists(h1_1967:exists(h2_1851:exists(v_bool_154_767':exists(n2_1850:exists(x:exists(p_1845:exists(h:exists(flted_150_86:exists(S2_1852:exists(v_1844:exists(S1_1968:exists(S2_1972:exists(v_1964:exists(S1_1848:(p_1965=xleft_1963 & 
  q_1969=q_1849 & h2_1971=h2_1851 & -1+h1=h1_1967 & h1_1960=h1_1967 & 1+
  h_1889=h & 1+h1_1847=h & 1+n1_1966+n2_1850=flted_150_86 & 
  n2_1970=n2_1850 & n1_1846+n2_1850=flted_150_86 & -1+n=flted_150_86 & 1+
  flted_150_1959+n2_1850=flted_150_86 & n2_1850+n_1888=flted_150_86 & 
  S2_1852=S2_1972 & S2_1962=S1_1968 & res=v_int_166_766' & S1_1848=S1_1892 & 
  s=sm_1840 & b=b_87 & lg_1841=b_87 & v_1844=v_1964 & 
  tmp_90'=v_int_166_766' & s1_1961=s1 & s_1890=sm_1840 & b_1891=pl_1842 & 
  x'=x & sm_1840<=v_int_166_766' & v_int_166_766'<=s1 & s1<=pl_1842 & 
  pl_1842<=v_1964 & v_1964<=qs_1843 & qs_1843<=b_87 & h2_1851<=h1_1967 & 
  0<=h1_1967 & (1+h1_1967)<=h & (1+n2_1850)<=flted_150_86 & 
  flted_150_86<=-2 & !(v_bool_154_767') & x!=null & p_1845!=null & 
  RMVM(S1_1892,S2_1962) & 2<=h | p_1965=xleft_1963 & q_1969=q_1849 & 
  h2_1971=h2_1851 & -1+h1=h1_1967 & h1_1960=h1_1967 & 1+h_1889=h & 1+
  h1_1847=h & 1+n1_1966+n2_1850=flted_150_86 & n2_1970=n2_1850 & n1_1846+
  n2_1850=flted_150_86 & -1+n=flted_150_86 & 1+flted_150_1959+
  n2_1850=flted_150_86 & n2_1850+n_1888=flted_150_86 & S2_1852=S2_1972 & 
  S2_1962=S1_1968 & res=v_int_166_766' & S1_1848=S1_1892 & s=sm_1840 & 
  b=b_87 & lg_1841=b_87 & v_1844=v_1964 & tmp_90'=v_int_166_766' & 
  s1_1961=s1 & s_1890=sm_1840 & b_1891=pl_1842 & x'=x & 
  sm_1840<=v_int_166_766' & v_int_166_766'<=s1 & s1<=pl_1842 & 
  pl_1842<=v_1964 & v_1964<=qs_1843 & qs_1843<=b_87 & h2_1851<=h1_1967 & 
  0<=h1_1967 & (1+h1_1967)<=h & !(v_bool_154_767') & (1+
  n2_1850)<=flted_150_86 & x!=null & p_1845!=null & RMVM(S1_1892,S2_1962) & 
  2<=h & 0<=flted_150_86 | p_1965=xleft_1963 & q_1969=q_1849 & 
  h2_1971=h2_1851 & -1+h=h2_1851 & -1+h1=h2_1851 & h1_1960=h1_1967 & 
  h1_1847=h_1889 & 1+n1_1966+n2_1850=flted_150_86 & n2_1970=n2_1850 & 
  n1_1846+n2_1850=flted_150_86 & -1+n=flted_150_86 & 1+flted_150_1959+
  n2_1850=flted_150_86 & n2_1850+n_1888=flted_150_86 & S2_1852=S2_1972 & 
  S2_1962=S1_1968 & res=v_int_166_766' & S1_1848=S1_1892 & s=sm_1840 & 
  b=b_87 & lg_1841=b_87 & v_1844=v_1964 & tmp_90'=v_int_166_766' & 
  s1_1961=s1 & s_1890=sm_1840 & b_1891=pl_1842 & x'=x & 
  sm_1840<=v_int_166_766' & v_int_166_766'<=s1 & s1<=pl_1842 & 
  pl_1842<=v_1964 & v_1964<=qs_1843 & qs_1843<=b_87 & 1<=h_1889 & 
  h1_1967<=h_1889 & (1+h_1889)<=h2_1851 & (1+n2_1850)<=flted_150_86 & 
  flted_150_86<=-2 & !(v_bool_154_767') & x!=null & p_1845!=null & 
  RMVM(S1_1892,S2_1962) | p_1965=xleft_1963 & q_1969=q_1849 & 
  h2_1971=h2_1851 & -1+h=h2_1851 & -1+h1=h2_1851 & h1_1960=h1_1967 & 
  h1_1847=h_1889 & 1+n1_1966+n2_1850=flted_150_86 & n2_1970=n2_1850 & 
  n1_1846+n2_1850=flted_150_86 & -1+n=flted_150_86 & 1+flted_150_1959+
  n2_1850=flted_150_86 & n2_1850+n_1888=flted_150_86 & S2_1852=S2_1972 & 
  S2_1962=S1_1968 & res=v_int_166_766' & S1_1848=S1_1892 & s=sm_1840 & 
  b=b_87 & lg_1841=b_87 & v_1844=v_1964 & tmp_90'=v_int_166_766' & 
  s1_1961=s1 & s_1890=sm_1840 & b_1891=pl_1842 & x'=x & 
  sm_1840<=v_int_166_766' & v_int_166_766'<=s1 & s1<=pl_1842 & 
  pl_1842<=v_1964 & v_1964<=qs_1843 & qs_1843<=b_87 & 1<=h_1889 & 
  h1_1967<=h_1889 & (1+h_1889)<=h2_1851 & !(v_bool_154_767') & (1+
  n2_1850)<=flted_150_86 & x!=null & p_1845!=null & RMVM(S1_1892,S2_1962) & 
  0<=flted_150_86 | p_1965=xleft_1963 & q_1969=q_1849 & h2_1971=h2_1851 & -1+
  h1=h2_1851 & h1_1960=h1_1967 & 1+h_1889=h & 1+h1_1847=h & 1+n1_1966+
  n2_1850=flted_150_86 & n2_1970=n2_1850 & n1_1846+n2_1850=flted_150_86 & -1+
  n=flted_150_86 & 1+flted_150_1959+n2_1850=flted_150_86 & n2_1850+
  n_1888=flted_150_86 & S2_1852=S2_1972 & S2_1962=S1_1968 & 
  res=v_int_166_766' & S1_1848=S1_1892 & s=sm_1840 & b=b_87 & lg_1841=b_87 & 
  v_1844=v_1964 & tmp_90'=v_int_166_766' & s1_1961=s1 & s_1890=sm_1840 & 
  b_1891=pl_1842 & x'=x & sm_1840<=v_int_166_766' & v_int_166_766'<=s1 & 
  s1<=pl_1842 & pl_1842<=v_1964 & v_1964<=qs_1843 & qs_1843<=b_87 & (1+
  h1_1967)<=h2_1851 & 0<=h2_1851 & (1+h2_1851)<=h & (1+
  n2_1850)<=flted_150_86 & flted_150_86<=-2 & !(v_bool_154_767') & x!=null & 
  p_1845!=null & RMVM(S1_1892,S2_1962) & 2<=h | p_1965=xleft_1963 & 
  q_1969=q_1849 & h2_1971=h2_1851 & -1+h1=h2_1851 & h1_1960=h1_1967 & 1+
  h_1889=h & 1+h1_1847=h & 1+n1_1966+n2_1850=flted_150_86 & 
  n2_1970=n2_1850 & n1_1846+n2_1850=flted_150_86 & -1+n=flted_150_86 & 1+
  flted_150_1959+n2_1850=flted_150_86 & n2_1850+n_1888=flted_150_86 & 
  S2_1852=S2_1972 & S2_1962=S1_1968 & res=v_int_166_766' & S1_1848=S1_1892 & 
  s=sm_1840 & b=b_87 & lg_1841=b_87 & v_1844=v_1964 & 
  tmp_90'=v_int_166_766' & s1_1961=s1 & s_1890=sm_1840 & b_1891=pl_1842 & 
  x'=x & sm_1840<=v_int_166_766' & v_int_166_766'<=s1 & s1<=pl_1842 & 
  pl_1842<=v_1964 & v_1964<=qs_1843 & qs_1843<=b_87 & (1+h1_1967)<=h2_1851 & 
  0<=h2_1851 & (1+h2_1851)<=h & !(v_bool_154_767') & (1+
  n2_1850)<=flted_150_86 & x!=null & p_1845!=null & RMVM(S1_1892,S2_1962) & 
  2<=h & 0<=flted_150_86) & S1=union(S1_1848,S2_1852,{v_1844}) & S1!=() & 
  S2=union(S1_1968,S2_1972,{v_1964}) & 
  S1_1848!=()))))))))))))))))))))))))))))))))))))))))))))) --> RMVM(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Checking procedure delete$node2~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

assert:bst_mshob.ss:186: 16:  : ok


[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure flatten$node2 SUCCESS

Checking procedure insert$node2~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
MONA translation failure!
Context of Verification Failure: File "bst_mshob.ss",Line:119,Col:10
Last Proving Location: File "bst_mshob.ss",Line:132,Col:19

ERROR: at _0_0 
Message: Mona translation failure!!
Error in file monatemp near line  syntax error
 
[mona.ml]:Unexpected exception

Procedure insert$node2~int FAIL-2

Exception Failure("Mona translation failure!!\nError in file monatemp near line  syntax error") Occurred!

Error(s) detected when checking procedure insert$node2~int

Checking procedure search$node2~int... 
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
Procedure traverse$node2 SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 14.84 second(s)
	Time spent in main process: 1.4 second(s)
	Time spent in child processes: 13.44 second(s)
