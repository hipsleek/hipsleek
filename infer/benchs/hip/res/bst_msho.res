
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


!!! REL :  DEL(sm,s,l,lg,a)
!!! POST:  l>=s & lg>=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; h; sm; 
                    lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{268,267}]&
                    (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::ref [x]
                                EXISTS(n1,h1,s,
                                l: x'::bst2<n1,h1,s,l>@M[Orig][LHSCase]@ rem br[{268,267}]&
                                (
                                ([0<=n1 & n1<=n][0<=h1 & h1<=h]
                                 [s<=l & DEL(sm,s,l,lg,a)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; sm; 
                  lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{268,267}]&
                  (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::ref [x]
                              EXISTS(n1_1679,h1_1680,s_1681,
                              l_1682: x'::bst2<n1_1679,h1_1680,s_1681,l_1682>@M[Orig][LHSCase]@ rem br[{268,267}]&
                              (
                              ([sm<=lg][s_1681<=l_1682]
                               [0<=h1_1680 & 0<=h & h1_1680<=h]
                               [0<=n1_1679 & 0<=n & n1_1679<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm=s & s<=l & l<=a & exists(qs_1232:a<=qs_1232 & 
  qs_1232<=lg)) --> DEL(sm,s,l,lg,a),
 (exists(qs_1232:qs_1232<=lg & a<=qs_1232 & l<=a & s=sm & 
  exists(pl_1402:exists(qs_1403:exists(v_1404:qs_1403<=l & sm<=pl_1402 & 
  pl_1402<=v_1404 & v_1404<=qs_1403))))) --> DEL(sm,s,l,lg,a),
 (false) --> DEL(sm,s,l,lg,a),
 (s=sm & a=sm & l=lg & exists(v_1526:exists(s1_1524:s1_1524<=lg & 
  sm<=v_1526 & v_1526<=s1_1524))) --> DEL(sm,s,l,lg,a),
 (DEL(sm_1281,s_1575,l_1576,lg_1282,a) & s_1575<=l & lg=lg_1282 & sm=s & 
  l_1576=l & sm_1281<=lg_1282 & exists(v_1233:(1+v_1233)<=a & 
  v_1233<=sm_1281 & v_1233<=s_1575 & exists(pl_1231:s<=pl_1231 & 
  pl_1231<=v_1233))) --> DEL(sm,s,l,lg,a),
 (DEL(sm_1299,s_1628,l_1629,lg_1300,a) & s<=l_1629 & s_1628=s & lg=l & 
  sm=sm_1299 & sm_1299<=lg_1300 & exists(v_1233:exists(qs_1232:qs_1232<=l & 
  (1+a)<=v_1233 & l_1629<=v_1233 & lg_1300<=v_1233 & 
  v_1233<=qs_1232))) --> DEL(sm,s,l,lg,a),
 (s<=l & sm<=lg) --> DEL(sm,s,l,lg,a)]
!!! NEW ASSUME:[ RELASS [DEL]: ( DEL(sm_1281,s_1575,l_1576,lg_1282,a)) -->  a<=(s_1575+1) | sm_1281<=s_1575 & s_1575<=(a-2) | l_1576<s_1575 & 
s_1575<=(a-2) & s_1575<=(sm_1281-1) | s_1575<=(a-2) & s_1575<=(sm_1281-1) & 
s_1575<=l_1576 & lg_1282<sm_1281,
 RELASS [DEL]: ( DEL(sm_1299,s_1628,l_1629,lg_1300,a)) -->  lg_1300<sm_1299 | sm_1299<=lg_1300 & l_1629<=lg_1300 | sm_1299<=lg_1300 & 
lg_1300<l_1629 & l_1629<s_1628 | sm_1299<=lg_1300 & lg_1300<l_1629 & 
l_1629<=(a+1) & s_1628<=l_1629]
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
                    lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{268,267}]&
                    (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::
                                EXISTS(flted_81_94,h1,mi,
                                ma: res::bst2<flted_81_94,h1,mi,ma>@M[Orig][LHSCase]@ rem br[{267}]&
                                (
                                ([0!=flted_81_94 & 0<=flted_81_94 & -1+
                                   flted_81_94=n]
                                 [0!=h1 & 0<=h1 & h<=h1][null!=res]
                                 [mi<=ma & C(mi,sm,lg,ma,a)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; sm; 
                  lg](ex)x::bst2<n,h,sm,lg>@M[Orig][LHSCase]@ rem br[{268,267}]&
                  (([0<=h][0<=n][sm<=lg]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::
                              EXISTS(flted_81_2198,h1_2199,mi_2200,
                              ma_2201: res::bst2<flted_81_2198,h1_2199,mi_2200,ma_2201>@M[Orig][LHSCase]@ rem br[{267}]&
                              (
                              ([(lg>=sm & ma_2201>=(1+lg) & sm=mi_2200 & 
                                 ma_2201=a | a>=(1+sm) & ma_2201>=a & 
                                 ma_2201=lg & sm=mi_2200 | sm>=a & 
                                 ma_2201>=sm & ma_2201=lg & a=mi_2200) & 
                                 mi_2200<=ma_2201 & sm<=lg]
                               [null!=res]
                               [0!=h1_2199 & 0<=h & h<=h1_2199 & 0<=h1_2199]
                               [0!=flted_81_2198 & 0<=n & -1+
                                 flted_81_2198=n & 0<=flted_81_2198]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=mi & ma=lg & mi<=sm & sm<=lg | mi=sm & ma=a & sm<=lg & lg<a | mi=sm & 
  ma=lg & sm<a & a<=lg) --> C(mi,sm,lg,ma,a),
 (C(mi_2026,sm_1994,lg_1995,ma_2027,a) & mi<=ma_2027 & mi_2026=mi & lg=ma & 
  sm=sm_1994 & sm_1994<=lg_1995 & exists(v_1973:exists(qs_1972:qs_1972<=ma & 
  a<=v_1973 & ma_2027<=v_1973 & lg_1995<=v_1973 & 
  v_1973<=qs_1972))) --> C(mi,sm,lg,ma,a),
 (C(mi_2067,sm_2035,lg_2036,ma_2068,a) & mi_2067<=ma & ma_2068=ma & 
  lg=lg_2036 & sm=mi & sm_2035<=lg_2036 & 
  exists(v_1973:exists(pl_1971:mi<=pl_1971 & (1+v_1973)<=a & 
  pl_1971<=v_1973 & v_1973<=sm_2035 & v_1973<=mi_2067))) --> C(mi,sm,lg,ma,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_2026,sm_1994,lg_1995,ma_2027,a)) -->  lg_1995<sm_1994 | sm_1994<=lg_1995 & ma_2027<mi_2026 | mi_2026<=ma_2027 & 
ma_2027<=lg_1995 & sm_1994<=lg_1995 | sm_1994<=lg_1995 & lg_1995<ma_2027 & 
ma_2027<=a & mi_2026<=ma_2027,
 RELASS [C]: ( C(mi_2067,sm_2035,lg_2036,ma_2068,a)) -->  a<=(mi_2067+1) | ma_2068<mi_2067 & mi_2067<=(a-2) | sm_2035<=mi_2067 & 
mi_2067<=(a-2) & mi_2067<=ma_2068 | mi_2067<=(a-2) & mi_2067<=ma_2068 & 
mi_2067<=(sm_2035-1) & lg_2036<sm_2035]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Checking procedure remove_min$node2... 
!!! REL :  RMVM(s,res,s1)
!!! POST:  res>=s & s1>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMVM]
              EBase exists (Expl)(Impl)[n; h; s; 
                    b](ex)x::bst2<n,h,s,b>@M[Orig][LHSCase]@ rem br[{267}]&(
                    ([null!=x][0<=h & 0!=h][0<=n & 0!=n][s<=b]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::ref [x]
                                EXISTS(b_83,flted_114_82,h1,
                                s1: x'::bst2<flted_114_82,h1,s1,b_83>@M[Orig][LHSCase]@ rem br[{268,267}]&
                                (
                                ([0<=flted_114_82 & 1+flted_114_82=n]
                                 [0<=h1 & h1<=h]
                                 [b=b_83 & s1<=b_83 & RMVM(s,res,s1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; s; 
                  b](ex)x::bst2<n,h,s,b>@M[Orig][LHSCase]@ rem br[{267}]&(
                  ([x!=null][1<=h][1<=n][s<=b]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              EXISTS(b_2351,flted_114_2352,h1_2353,
                              s1_2354: x'::bst2<flted_114_2352,h1_2353,s1_2354,b_2351>@M[Orig][LHSCase]@ rem br[{268,267}]&
                              (
                              ([b=b_2351 & s1_2354<=b_2351 & s<=b & 
                                 res<=s1_2354 & s<=res]
                               [0<=h1_2353 & 0<=h & h1_2353<=h]
                               [0<=flted_114_2352 & 0<=n & 1+flted_114_2352=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res<=s1 & exists(pl_2244:s<=pl_2244 & pl_2244<=res) & 
  exists(b:s1<=b)) --> RMVM(s,res,s1),
 (RMVM(s_2272,tmp_86',s1_2306) & s=s_2272 & s1_2306=s1 & 
  exists(pl_2244:exists(qs_2245:exists(b:exists(v_2246:s1<=pl_2244 & 
  s_2272<=pl_2244 & qs_2245<=b & pl_2244<=v_2246 & v_2246<=qs_2245)))) & 
  tmp_86'=res) --> RMVM(s,res,s1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Checking procedure search$node2~int... 
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 1760 invocations 
0 false contexts at: ()

Total verification time: 4.29 second(s)
	Time spent in main process: 0.47 second(s)
	Time spent in child processes: 3.82 second(s)
