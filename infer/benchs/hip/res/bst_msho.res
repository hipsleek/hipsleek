
Processing file "bst_msho.ss"
Parsing bst_msho.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
Procedure append$node2~node2 SUCCESS

Checking procedure count$node2... 
Procedure count$node2 SUCCESS

Checking procedure delete$node2~int... 
assert:bst_msho.ss:153: 16:  : ok


!!! REL :  DEL(sm,s,l,lg)
!!! POST:  s>=sm & l>=s & lg>=l
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; h; sm; 
                    lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{272,271}]&
                    (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::ref [x]
                                EXISTS(n1,h1,s,
                                l: x'::bst2<n1,h1,s,l>@M[Orig][LHSCase]@ rem br[{272,271}]&
                                (
                                ([0<=n1 & n1<=n][0<=h1 & h1<=h]
                                 [s<=l & DEL(sm,s,l,lg)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; sm; 
                  lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{272,271}]&
                  (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::ref [x]
                              EXISTS(n1_1702,h1_1703,s_1704,
                              l_1705: x'::bst2<n1_1702,h1_1703,s_1704,l_1705>@M[Orig][LHSCase]@ rem br[{272,271}]&
                              (
                              ([l_1705<=lg & sm<=lg & sm<=s_1704 & 
                                 s_1704<=l_1705]
                               [0<=h1_1703 & 0<=h & h1_1703<=h]
                               [0<=n1_1702 & 0<=n & n1_1702<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (s=sm & sm<=l & l<=lg) --> DEL(sm,s,l,lg),
 (s=sm & sm<=l & l<=lg) --> DEL(sm,s,l,lg),
 (false) --> DEL(sm,s,l,lg),
 (sm=s & lg=l & s<=l) --> DEL(sm,s,l,lg),
 (l=l_1599 & s=sm & lg_1305=lg & sm<=s_1598 & s_1598<=l_1599 & sm<=sm_1304 & 
  sm_1304<=lg & DEL(sm_1304,s_1598,l_1599,lg_1305)) --> DEL(sm,s,l,lg),
 (s=s_1651 & l=lg & sm_1322=sm & s_1651<=l_1652 & l_1652<=lg & sm<=lg_1323 & 
  lg_1323<=lg & DEL(sm_1322,s_1651,l_1652,lg_1323)) --> DEL(sm,s,l,lg),
 (sm<=s & s<=l & l<=lg) --> DEL(sm,s,l,lg)]
!!! NEW ASSUME:[ RELASS [DEL]: ( DEL(sm_1304,s_1598,l_1599,lg_1305)) -->  l_1599<s_1598 | sm_1304<=s_1598 & s_1598<=l_1599 | s_1598<=l_1599 & 
s_1598<=(sm_1304-1) & lg_1305<sm_1304,
 RELASS [DEL]: ( DEL(sm_1322,s_1651,l_1652,lg_1323)) -->  l_1652<=lg_1323 | lg_1323<l_1652 & l_1652<s_1651 | lg_1323<=(l_1652-1) & 
lg_1323<=(sm_1322-1) & s_1651<=l_1652]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
Procedure flatten$node2 SUCCESS

Checking procedure insert$node2~int... 
!!! REL :  C(mi,sm,lg,ma,a)
!!! POST:  lg>=sm & ma>=(1+lg) & sm=mi & ma=a | a>=(1+sm) & ma>=a & ma=lg & sm=mi | 
sm>=a & ma>=sm & ma=lg & a=mi
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[n; h; sm; 
                    lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{272,271}]&
                    (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::
                                EXISTS(flted_81_100,h1,mi,
                                ma: res::bst2<flted_81_100,h1,mi,ma>@M[Orig][LHSCase]@ rem br[{271}]&
                                (
                                ([0!=flted_81_100 & 0<=flted_81_100 & -1+
                                   flted_81_100=n]
                                 [0!=h1 & 0<=h1 & h<=h1][null!=res]
                                 [mi<=ma & C(mi,sm,lg,ma,a)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; sm; 
                  lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{272,271}]&
                  (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::
                              EXISTS(flted_81_2221,h1_2222,mi_2223,
                              ma_2224: res::bst2<flted_81_2221,h1_2222,mi_2223,ma_2224>@M[Orig][LHSCase]@ rem br[{271}]&
                              (
                              ([(lg>=sm & ma_2224>=(1+lg) & sm=mi_2223 & 
                                 ma_2224=a | a>=(1+sm) & ma_2224>=a & 
                                 ma_2224=lg & sm=mi_2223 | sm>=a & 
                                 ma_2224>=sm & ma_2224=lg & a=mi_2223) & 
                                 mi_2223<=ma_2224 & sm<=lg]
                               [null!=res]
                               [0!=h1_2222 & 0<=h & h<=h1_2222 & 0<=h1_2222]
                               [0!=flted_81_2221 & 0<=n & -1+
                                 flted_81_2221=n & 0<=flted_81_2221]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg | mi=sm & ma=a & sm<=lg & lg<a | mi=sm & 
  ma=lg & sm<a & a<=lg) --> C(mi,sm,lg,ma,a),
 (mi=mi_2049 & ma=lg & sm_2017=sm & mi_2049<=ma_2050 & ma_2050<=lg & 
  sm<=lg_2018 & lg_2018<=lg & a<=lg & 
  C(mi_2049,sm_2017,lg_2018,ma_2050,a)) --> C(mi,sm,lg,ma,a),
 (ma=ma_2091 & mi=sm & lg_2059=lg & sm<=(a-1) & sm<=sm_2058 & sm<=mi_2090 & 
  mi_2090<=ma_2091 & sm_2058<=lg & 
  C(mi_2090,sm_2058,lg_2059,ma_2091,a)) --> C(mi,sm,lg,ma,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_2049,sm_2017,lg_2018,ma_2050,a)) -->  lg_2018<sm_2017 | sm_2017<=lg_2018 & ma_2050<mi_2049 | mi_2049<=ma_2050 & 
ma_2050<=lg_2018 & sm_2017<=lg_2018 | sm_2017<=lg_2018 & lg_2018<ma_2050 & 
ma_2050<=a & mi_2049<=ma_2050,
 RELASS [C]: ( C(mi_2090,sm_2058,lg_2059,ma_2091,a)) -->  a<=(mi_2090+1) | ma_2091<mi_2090 & mi_2090<=(a-2) | sm_2058<=mi_2090 & 
mi_2090<=(a-2) & mi_2090<=ma_2091 | mi_2090<=(a-2) & mi_2090<=ma_2091 & 
mi_2090<=(sm_2058-1) & lg_2059<sm_2058]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Checking procedure remove_min$node2... 
!!! REL :  RMVM(s,res,s1)
!!! POST:  res>=s & s1>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMVM]
              EBase exists (Expl)(Impl)[n; h; s; 
                    b](ex)x::bst2<n,h,s,b>@M[Orig][LHSCase]@ rem br[{271}]&(
                    ([null!=x][0<=h & 0!=h][0<=n & 0!=n][s<=b]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::ref [x]
                                EXISTS(b_89,flted_114_88,h1,
                                s1: x'::bst2<flted_114_88,h1,s1,b_89>@M[Orig][LHSCase]@ rem br[{272,271}]&
                                (
                                ([0<=flted_114_88 & 1+flted_114_88=n]
                                 [0<=h1 & h1<=h]
                                 [b=b_89 & s1<=b_89 & RMVM(s,res,s1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; s; 
                  b](ex)x::bst2<n,h,s,b>@M[Orig][LHSCase]@ rem br[{271}]&(
                  ([x!=null][1<=h][1<=n][s<=b]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              EXISTS(b_2374,flted_114_2375,h1_2376,
                              s1_2377: x'::bst2<flted_114_2375,h1_2376,s1_2377,b_2374>@M[Orig][LHSCase]@ rem br[{272,271}]&
                              (
                              ([b=b_2374 & s1_2377<=b_2374 & s<=b & 
                                 res<=s1_2377 & s<=res]
                               [0<=h1_2376 & 0<=h & h1_2376<=h]
                               [0<=flted_114_2375 & 0<=n & 1+flted_114_2375=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (s<=res & res<=s1) --> RMVM(s,res,s1),
 (s1=s1_2329 & tmp_92'=res & s_2295=s & 
  RMVM(s_2295,tmp_92',s1_2329)) --> RMVM(s,res,s1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Checking procedure search$node2~int... 
!!! REL :  SEARCH(sm,a,lg)
!!! POST:  a>=sm & lg>=a
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SEARCH]
              EBase exists (Expl)(Impl)[n; h; sm; 
                    lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{272,271}]&
                    (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                
                                EXISTS(n_64,h_65,sm_66,
                                lg_67: x::bst2<n_64,h_65,sm_66,lg_67>@M[Orig][LHSCase]@ rem br[{272,271}]&
                                (
                                ([!(res)][n=n_64 & 0<=n_64][h=h_65 & 0<=h_65]
                                 [sm_66=sm & lg=lg_67 & sm_66<=lg_67]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(n_68,h_69,sm_70,
                                   lg_71: x::bst2<n_68,h_69,sm_70,lg_71>@M[Orig][LHSCase]@ rem br[{272,271}]&
                                   (
                                   ([res][n=n_68 & 0<=n_68][h=h_69 & 0<=h_69]
                                    [sm=sm_70 & lg=lg_71 & sm_70<=lg_71 & 
                                      SEARCH(sm,a,lg)]
                                    ))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; sm; 
                  lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{272,271}]&
                  (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              
                              EXISTS(n_2967,h_2968,sm_2969,
                              lg_2970: x::bst2<n_2967,h_2968,sm_2969,lg_2970>@M[Orig][LHSCase]@ rem br[{272,271}]&
                              (
                              ([lg=lg_2970 & sm=sm_2969 & sm<=lg]
                               [h=h_2968 & 0<=h][n=n_2967 & 0<=n][!(res)]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n_2971,h_2972,sm_2973,
                                 lg_2974: x::bst2<n_2971,h_2972,sm_2973,lg_2974>@M[Orig][LHSCase]@ rem br[{272,271}]&
                                 (
                                 ([lg=lg_2974 & sm=sm_2973 & sm<=lg & 
                                    a<=lg & sm<=a]
                                  [h=h_2972 & 0<=h][n=n_2971 & 0<=n][
                                  res]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (sm<=a & a<=lg) --> SEARCH(sm,a,lg)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 2239 invocations 
0 false contexts at: ()

Total verification time: 4.66 second(s)
	Time spent in main process: 0.56 second(s)
	Time spent in child processes: 4.1 second(s)
