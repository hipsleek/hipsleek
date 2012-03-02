/usr/local/bin/mona

Processing file "dll_msb.ss"
Parsing dll_msb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure append2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP2(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{530}] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&(
                    ([0!=m][null!=x][S1!=()][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                EXISTS(q_217,t,
                                S: x::dll<q_217,t,S>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([t=m+n][APP2(S,S1,S2)][q=q_217]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{530}] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              EXISTS(q_2071,t_2072,
                              S_2073: x::dll<q_2071,t_2072,S_2073>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([S_2073=union(S1,S2)][q=q_2071]
                               [t_2072=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1963:exists(v_1808:exists(v_1961:exists(S1_1810:S1!=() & S2= & 
  S=union(S1_1963,{v_1961}) & S1=union(S1_1810,{v_1808}) & S1_1963=S2 & 
  v_1808=v_1961 & S1_1810=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1807:exists(m:exists(p_1805:exists(q_217:exists(q:exists(self_1868:exists(p_1867:exists(p:exists(v_1921:exists(S1_1923:exists(n:exists(q_1871:exists(q_1922:exists(q_1908:exists(x:exists(flted_12_1869:exists(q_1809:exists(y:exists(self_1806:exists(v_bool_188_1427':exists(v_bool_186_1432':exists(t:exists(S1_1909:exists(v_1907:exists(S1_1810:exists(v_1808:exists(S1_1872:exists(v_1870:S1_1909=union(S1_1923,
  {v_1921}) & S1_1810= & (flted_12_1807=0 & m=1 & p_1805=q & q_217=q & 
  self_1868=y & p_1867=p & v_1907=v_1808 & v_1921=v_1870 & S1_1872=S1_1923 & 
  1+n=t & q_1871=q_1922 & q_1908=y & x=self_1806 & 2+flted_12_1869=t & 
  q_1809=null & t<=0 & y!=null & self_1806!=null & 1<=v_bool_188_1427' & 
  1<=v_bool_186_1432' | flted_12_1807=0 & m=1 & p_1805=q & q_217=q & 
  self_1868=y & p_1867=p & v_1907=v_1808 & v_1921=v_1870 & S1_1872=S1_1923 & 
  1+n=t & q_1871=q_1922 & q_1908=y & x=self_1806 & 2+flted_12_1869=t & 
  q_1809=null & y!=null & self_1806!=null & 1<=v_bool_188_1427' & 
  1<=v_bool_186_1432' & 2<=t) & S2!=() & S=union(S1_1909,{v_1907}) & 
  S1=union(S1_1810,{v_1808}) & S2=union(S1_1872,{v_1870}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1810:exists(v_1808:exists(S1_1963:exists(v_1961:S1_1810= & 
  v_1808=v_1961 & S2=S1_1963 & S1=union(S1_1810,{v_1808}) & S=union(S1_1963,
  {v_1961}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1993:exists(v_1991:exists(S1_1810:exists(v_1808:S_1990!=() & 
  S1_1810!=() & S1_1810=S1_1881 & v_1808=v_1991 & S_1990=S1_1993 & 
  S2_1884=S2 & APP2(S_1990,S1_1881,S2_1884) & S1!=() & S=union(S1_1993,
  {v_1991}) & S1=union(S1_1810,{v_1808})))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure create_list$int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 55::
                                EXISTS(p_197,m,
                                S1: x::dll<p_197,m,S1>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([DEL(S,S1)][p=p_197][true]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 55::
                              EXISTS(p_2763,m_2764,
                              S1_2765: x::dll<p_2763,m_2764,S1_2765>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (([p=p_2763][S1_2765<subset> S ][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_2625:exists(v_2623:exists(S1_2498:exists(v_2496:exists(S1_2416:exists(v_2414:exists(S1_2611:exists(v_2609:exists(S1_2371:exists(v_2369:S1_2498=S1_2625 & 
  v_2623=v_2496 & S1_2611=union(S1_2625,{v_2623}) & S1_2416!=() & 
  S1_2371!=() & S1_2416=union(S1_2498,{v_2496}) & S1_2371=union(S1_2416,
  {v_2414}) & v_2369=v_2609 & S!=() & S1=union(S1_2611,{v_2609}) & 
  S=union(S1_2371,{v_2369})))))))))))) --> DEL(S,S1),
 (exists(S1_2416:exists(v_2414:exists(S1_2674:exists(v_2672:exists(S1_2371:exists(v_2369:S1_2416= & 
  S1_2371!=() & S1_2371=union(S1_2416,{v_2414}) & S1_2674= & v_2672=v_2369 & 
  S1=union(S1_2674,{v_2672}) & S!=() & S=union(S1_2371,
  {v_2369})))))))) --> DEL(S,S1),
 (exists(m:exists(flted_12_2558:exists(n:exists(a:exists(q_2560:exists(p_2556:exists(p:exists(p_197:exists(x:exists(p_2574:exists(v_int_299_2697:exists(n_2575:exists(tmp_199':exists(v_bool_287_1241':exists(self_2557:exists(m_2695:exists(q_2699:exists(S1_2561:exists(v_2559:exists(S1_2700:exists(v_2698:S1_2561!=() & 
  S1_2696!=() & (-1+m=m_2695 & flted_12_2558=n_2575 & -1+n=n_2575 & -1+
  a=v_int_299_2697 & q_2560=q_2699 & S1_2696=S1_2700 & S1_2561=S_2576 & 
  v_2698=v_2559 & p_2556=p_197 & p=p_197 & x=self_2557 & p_2574=self_2557 & 
  1<=v_int_299_2697 & (1+v_int_299_2697)<=n_2575 & m_2695<=-1 & 
  tmp_199'=null & !(v_bool_287_1241') & self_2557!=null & q_2699!=null & 
  DEL(S_2576,S1_2696) | -1+m=m_2695 & flted_12_2558=n_2575 & -1+n=n_2575 & 
  -1+a=v_int_299_2697 & q_2560=q_2699 & S1_2696=S1_2700 & S1_2561=S_2576 & 
  v_2698=v_2559 & p_2556=p_197 & p=p_197 & x=self_2557 & p_2574=self_2557 & 
  1<=v_int_299_2697 & (1+v_int_299_2697)<=n_2575 & tmp_199'=null & 
  !(v_bool_287_1241') & self_2557!=null & 1<=m_2695 & q_2699!=null & 
  DEL(S_2576,S1_2696)) & S!=() & S=union(S1_2561,{v_2559}) & 
  S1=union(S1_2700,{v_2698}))))))))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FGE(S,m)
!!! POST:  m <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[Anon_76; n; 
                    S](ex)x::dll<Anon_76,n,S>@M[Orig][LHSCase]@ rem br[{531,530}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 132::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_77,Anon_78,
                                   m: res::node<m,Anon_77,Anon_78>@M[Orig][]&
                                   (([FGE(S,m) & (1+v)<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_76; n; 
                  S](ex)x::dll<Anon_76,n,S>@M[Orig][LHSCase]@ rem br[{531,530}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 132::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_3318,Anon_3319,
                                 m_3320: res::node<m_3320,Anon_3318,Anon_3319>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_3320 & m_3320 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_3225:exists(Anon_76:exists(Anon_77:exists(Anon_78:exists(q_3229:exists(self_3226:exists(flted_12_3227:exists(v_bool_530_829':exists(v:exists(v_node_534_822':exists(v_bool_533_828':exists(n:exists(S1_3230:exists(v_3228:(x=v_node_534_822' & 
  res=v_node_534_822' & p_3225=Anon_77 & Anon_76=Anon_77 & Anon_78=q_3229 & 
  m=v_3228 & self_3226=v_node_534_822' & 1+flted_12_3227=n & 
  v_bool_530_829'<=0 & (1+v)<=v_3228 & n<=-1 & v_node_534_822'!=null & 
  1<=v_bool_533_828' | x=v_node_534_822' & res=v_node_534_822' & 
  p_3225=Anon_77 & Anon_76=Anon_77 & Anon_78=q_3229 & m=v_3228 & 
  self_3226=v_node_534_822' & 1+flted_12_3227=n & v_bool_530_829'<=0 & (1+
  v)<=v_3228 & v_node_534_822'!=null & 1<=v_bool_533_828' & 1<=n) & S!=() & 
  S=union(S1_3230,{v_3228})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_3230:exists(v_3228:v_3228<=v & S1_3230=S_3256 & 
  m_3294=m & (1+v)<=m & FGE(S_3256,m_3294) & S=union(S1_3230,{v_3228}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[Anon_43; n; 
                    S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{530}]&
                    (([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::ref [x]
                                EXISTS(flted_213_213,flted_213_214,Anon_44,
                                Anon_45,S1,
                                S2: x'::dll<Anon_44,flted_213_214,S1>@M[Orig][LHSCase]@ rem br[{530}] * 
                                res::dll<Anon_45,flted_213_213,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (
                                ([1=flted_213_214][1+flted_213_213=n]
                                 [S1!=() & GN(S,S1,S2)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_43; n; 
                  S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::ref [x]
                              EXISTS(flted_213_3427,flted_213_3428,Anon_3429,
                              Anon_3430,S1_3431,
                              S2_3432: x'::dll<Anon_3429,flted_213_3428,S1_3431>@M[Orig][LHSCase]@ rem br[{530}] * 
                              res::dll<Anon_3430,flted_213_3427,S2_3432>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([S1_3431!=() & union(S1_3431,S2_3432)=S]
                               [null!=x'][1+flted_213_3427=n & 0<=n]
                               [1=flted_213_3428]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_213_214:exists(q_3375:exists(tmp_215':exists(res:exists(q_3355:exists(v_node_218_1388':exists(Anon_43:exists(p_3351:exists(self_3352:exists(x':exists(n:exists(next_217_3373:exists(prev_217_1386':exists(x:exists(flted_213_213:exists(next_216_1383':exists(Anon_44:exists(Anon_45:exists(flted_12_3353:exists(S1_3356:exists(v_3354:exists(S1_3376:exists(v_3374:S1_3376= & 
  (flted_213_214=1 & q_3375=next_216_1383' & tmp_215'=v_node_218_1388' & 
  res=v_node_218_1388' & q_3355=v_node_218_1388' & Anon_43=p_3351 & 
  self_3352=Anon_45 & x'=Anon_45 & -1+n=flted_12_3353 & v_3374=v_3354 & 
  S1_3356=S2 & next_217_3373=next_216_1383' & prev_217_1386'=Anon_44 & 
  x=Anon_45 & flted_213_213=flted_12_3353 & next_216_1383'=null & 
  Anon_44=null & flted_12_3353<=-2 & Anon_45!=null | flted_213_214=1 & 
  q_3375=next_216_1383' & tmp_215'=v_node_218_1388' & res=v_node_218_1388' & 
  q_3355=v_node_218_1388' & Anon_43=p_3351 & self_3352=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_3353 & v_3374=v_3354 & S1_3356=S2 & 
  next_217_3373=next_216_1383' & prev_217_1386'=Anon_44 & x=Anon_45 & 
  flted_213_213=flted_12_3353 & next_216_1383'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_3353) & S=union(S1_3356,{v_3354}) & 
  S1=union(S1_3376,{v_3374}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
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
              EBase exists (Expl)(Impl)[Anon_62; n; 
                    S](ex)x::dll<Anon_62,n,S>@M[Orig][LHSCase]@ rem br[{530}]&
                    (([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(flted_259_202,Anon_63,
                                S2: res::dll<Anon_63,flted_259_202,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([2+flted_259_202=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_62; n; 
                  S](ex)x::dll<Anon_62,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(flted_259_3527,Anon_3528,
                              S2_3529: res::dll<Anon_3528,flted_259_3527,S2_3529>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([2+flted_259_3527=n & 0<=n]
                               [S2_3529<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_3504:exists(S1_3506:exists(S1_3463:exists(v_3461:S1_3463=union(S1_3506,
  {v_3504}) & S1_3463!=() & S2=S1_3506 & S!=() & S=union(S1_3463,
  {v_3461})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INSERT(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(p_200,m,
                                S1: x::dll<p_200,m,S1>@M[Orig][LHSCase]@ rem br[{530}]&
                                (
                                ([-1+m=n][S1!=() & INSERT(S,S1,a)][p=p_200]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              EXISTS(p_3694,m_3695,
                              S1_3696: x::dll<p_3694,m_3695,S1_3696>@M[Orig][LHSCase]@ rem br[{530}]&
                              (
                              ([S1_3696!=() & S1_3696=union(S,{a})][null!=x]
                               [p=p_3694][-1+m_3695=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3622:exists(v_3620:exists(S1_3608:exists(v_3606:exists(S1_3561:exists(v_3559:S1_3622= & 
  S1_3608=union(S1_3622,{v_3620}) & S1_3561= & v_3559=v_3606 & v_3620=a & 
  S1=union(S1_3608,{v_3606}) & S=union(S1_3561,{v_3559}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3649:exists(v_3647:exists(S1_3561:exists(v_3559:S1_3561!=() & 
  S1_3646!=() & v_3647=v_3559 & S1_3561=S_3589 & S1_3646=S1_3649 & 
  INSERT(S_3589,S1_3646,a) & S!=() & S1=union(S1_3649,{v_3647}) & 
  S=union(S1_3561,{v_3559})))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; n; 
                    S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{531,530}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 97::
                                EXISTS(p_176,n_177,
                                S2: x::dll<p_176,n_177,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([TRAV(S1,S2)][p=p_176][n=n_177]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{531,530}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 97::
                              EXISTS(p_5257,n_5258,
                              S2_5259: x::dll<p_5257,n_5258,S2_5259>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (([S1=S2_5259][n=n_5258 & 0<=n][p=p_5257]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_5217:exists(v_5215:exists(S1_5191:exists(v_5189:v_5215=v_5189 & 
  S1_5191=S1_5197 & S2_5214=S1_5217 & TRAV(S1_5197,S2_5214) & S1!=() & 
  S2=union(S1_5217,{v_5215}) & S1=union(S1_5191,
  {v_5189})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_39; m; 
                    S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{530}]&
                    (([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 24::ref [x]
                                EXISTS(flted_117_220,Anon_40,
                                S2: x'::dll<Anon_40,flted_117_220,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([1+flted_117_220=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39; m; 
                  S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{530}]&
                  (([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 24::ref [x]
                              EXISTS(flted_117_5451,Anon_5452,
                              S2_5453: x'::dll<Anon_5452,flted_117_5451,S2_5453>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([1+flted_117_5451=m & 0<=m]
                               [S2_5453<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_5292:exists(v_5290:S1_5292= & S2= & S1=union(S1_5292,{v_5290}) & 
  S1!=()))) --> PF(S1,S2),
 (exists(q_5356:exists(q_5381:exists(Anon_39:exists(p_5287:exists(self_5353:exists(v_node_129_1472':exists(x:exists(res:exists(tmp_221':exists(v_5355:exists(S1_5357:exists(flted_12_5289:exists(m:exists(Anon_40:exists(self_5288:exists(q_5291:exists(flted_12_5354:exists(next_128_1471':exists(prev_126_1463':exists(v_bool_120_1473':exists(p_5352:exists(x':exists(flted_117_220:exists(S1_5382:exists(v_5380:exists(S1_5292:exists(v_5290:S1_5292!=() & 
  S1_5292=union(S1_5357,{v_5355}) & (q_5356=q_5381 & Anon_39=p_5287 & 
  self_5353=x' & v_node_129_1472'=p_5352 & x=p_5352 & res=p_5352 & 
  tmp_221'=p_5352 & v_5380=v_5355 & S1_5357=S1_5382 & 
  flted_12_5289=flted_117_220 & -1+m=flted_117_220 & 
  Anon_40=prev_126_1463' & self_5288=p_5352 & q_5291=x' & 1+
  flted_12_5354=flted_117_220 & next_128_1471'=null & prev_126_1463'=null & 
  flted_117_220<=-2 & v_bool_120_1473'<=0 & p_5352!=null & x'!=null | 
  q_5356=q_5381 & Anon_39=p_5287 & self_5353=x' & v_node_129_1472'=p_5352 & 
  x=p_5352 & res=p_5352 & tmp_221'=p_5352 & v_5380=v_5355 & 
  S1_5357=S1_5382 & flted_12_5289=flted_117_220 & -1+m=flted_117_220 & 
  Anon_40=prev_126_1463' & self_5288=p_5352 & q_5291=x' & 1+
  flted_12_5354=flted_117_220 & next_128_1471'=null & prev_126_1463'=null & 
  v_bool_120_1473'<=0 & p_5352!=null & x'!=null & 1<=flted_117_220) & 
  S1!=() & S2=union(S1_5382,{v_5380}) & S1=union(S1_5292,
  {v_5290}))))))))))))))))))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  PUF(S1,S)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_36; n; 
                    S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{531,530}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(v_222,n_223,Anon_37,q,Anon_38,
                                S1: x'::node<v_222,Anon_37,q>@M[Orig][] * 
                                q::dll<Anon_38,n_223,S1>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([PUF(S1,S)][v=v_222][n=n_223][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36; n; 
                  S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{531,530}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(v_5566,n_5567,Anon_5568,q_5569,
                              Anon_5570,
                              S1_5571: x'::node<v_5566,Anon_5568,q_5569>@M[Orig][] * 
                              q_5569::dll<Anon_5570,n_5567,S1_5571>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([S=S1_5571][x'!=null][n=n_5567 & 0<=n]
                               [v=v_5566]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> PUF(S1,S),
 (exists(q_5493:exists(q_5511:exists(v:exists(v_222:exists(n:exists(Anon_38:exists(p_5489:exists(Anon_37:exists(Anon_36:exists(self_5490:exists(q:exists(x':exists(flted_12_5491:exists(v_bool_101_1494':exists(x:exists(tmp_224':exists(n_223:exists(S1_5494:exists(v_5492:exists(S1_5512:exists(v_5510:(q_5493=q_5511 & 
  v=v_222 & n=n_223 & v_5510=v_5492 & S1_5494=S1_5512 & Anon_38=Anon_36 & 
  p_5489=Anon_36 & Anon_37=Anon_36 & self_5490=x & q=x & x'=tmp_224' & 1+
  flted_12_5491=n_223 & n_223<=-1 & v_bool_101_1494'<=0 & x!=null & 
  tmp_224'!=null | q_5493=q_5511 & v=v_222 & n=n_223 & v_5510=v_5492 & 
  S1_5494=S1_5512 & Anon_38=Anon_36 & p_5489=Anon_36 & Anon_37=Anon_36 & 
  self_5490=x & q=x & x'=tmp_224' & 1+flted_12_5491=n_223 & 
  v_bool_101_1494'<=0 & x!=null & tmp_224'!=null & 1<=n_223) & S!=() & 
  S=union(S1_5494,{v_5492}) & S1=union(S1_5512,
  {v_5510}))))))))))))))))))))))) --> PUF(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_41; n; 
                    S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{531,530}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                EXISTS(n_216,Anon_42,
                                S2: x::dll<Anon_42,n_216,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([n=n_216]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_41; n; 
                  S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{531,530}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              EXISTS(Anon_5577,n_5578,
                              S2_5579: x::dll<Anon_5577,n_5578,S2_5579>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([n=n_5578 & 0<=n][S1=S2_5579][res=x]
                               [Anon_5577=Anon_41]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SN(S,S2)
!!! POST:  S=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                    Anon_49; j; 
                    S](ex)EXISTS(x_207: x::node<v,Anon_46,t>@M[Orig][] * 
                    t::dll<x_207,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{531,530}] * 
                    y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{531,530}]&(
                    ([x=x_207 & x!=null][0<=Anon_47][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::ref [x]
                                EXISTS(v_208,y_209,j_210,Anon_50,Anon_51,
                                S2: x::node<v_208,Anon_50,y_209>@M[Orig][] * 
                                y::dll<Anon_51,j_210,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (
                                ([SN(S,S2)][v=v_208][y=y_209][j=j_210]
                                 [x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                  Anon_49; j; S](ex)x::node<v,Anon_46,t>@M[Orig][] * 
                  t::dll<x_207,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{531,530}] * 
                  y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{531,530}]&(
                  ([x=x_207 & x!=null][0<=Anon_47]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::ref [x]
                              EXISTS(v_6084,y_6085,j_6086,Anon_6088,
                              S2_6089: y::dll<Anon_6088,j_6086,S2_6089>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([S=S2_6089][x!=null][j=j_6086 & 0<=j]
                               [y=y_6085][v=v_6084][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S) --> SN(S,S2),
 (S=S2 & S2=) --> SN(S,S2),
 (exists(q_6010:exists(q_6026:exists(Anon_50:exists(Anon_46:exists(x_5959:exists(x':exists(self_6007:exists(p_6006:exists(Anon_49:exists(j:exists(v:exists(v_208:exists(y_209:exists(x:exists(flted_12_6008:exists(v_bool_228_1360':exists(y:exists(Anon_51:exists(Anon_47:exists(j_210:exists(S1_6011:exists(v_6009:exists(S1_6027:exists(v_6025:(q_6010=q_6026 & 
  Anon_50=Anon_46 & x_5959=Anon_51 & x'=Anon_51 & self_6007=y & 
  p_6006=Anon_49 & v_6025=v_6009 & S1_6011=S1_6027 & j=j_210 & v=v_208 & 
  y_209=y & x=Anon_51 & 1+flted_12_6008=j_210 & j_210<=-1 & 
  v_bool_228_1360'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 | 
  q_6010=q_6026 & Anon_50=Anon_46 & x_5959=Anon_51 & x'=Anon_51 & 
  self_6007=y & p_6006=Anon_49 & v_6025=v_6009 & S1_6011=S1_6027 & j=j_210 & 
  v=v_208 & y_209=y & x=Anon_51 & 1+flted_12_6008=j_210 & 
  v_bool_228_1360'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 & 1<=j_210) & 
  S!=() & S=union(S1_6011,{v_6009}) & S2=union(S1_6027,
  {v_6025})))))))))))))))))))))))))) --> SN(S,S2)]
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
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure size$node SUCCESS

Checking procedure splice$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 90::ref [x]
                                EXISTS(p_179,Anon_71,n2,n1,S1,
                                S2: x'::dll<p_179,n1,S1>@M[Orig][LHSCase]@ rem br[{530}] * 
                                res::dll<Anon_71,n2,S2>@M[Orig][LHSCase]@ rem br[{530}]&
                                (
                                ([a=n1 & 0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][p=p_179]
                                 [null!=x'][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{530}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 90::ref [x]
                              EXISTS(p_6926,Anon_6927,n2_6928,n1_6929,
                              S1_6930,
                              S2_6931: x'::dll<p_6926,n1_6929,S1_6930>@M[Orig][LHSCase]@ rem br[{530}] * 
                              res::dll<Anon_6927,n2_6928,S2_6931>@M[Orig][LHSCase]@ rem br[{530}]&
                              (
                              ([S1_6930!=() & S2_6931!=() & union(S1_6930,
                                 S2_6931)=S]
                               [null!=res][null!=x'][p=p_6926]
                               [a=n1_6929 & 0!=n1_6929 & 0<=n & n=n1_6929+
                                 n2_6928 & 0!=n2_6928]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_6720:exists(v_6718:exists(S1_6815:exists(v_6813:S1_6720!=() & 
  S1_6815= & v_6718=v_6813 & S2=S1_6720 & S=union(S1_6720,{v_6718}) & 
  S!=() & S1=union(S1_6815,{v_6813})))))) --> SPLIT(S,S1,S2),
 (exists(S1_6859:exists(v_6857:exists(S1_6769:exists(v_6767:S1_6769!=() & 
  S2_6854!=() & S1_6853!=() & v_6857=v_6767 & S1_6769=S_6772 & 
  S1_6853=S1_6859 & S2_6854=S2 & SPLIT(S_6772,S1_6853,S2_6854) & S!=() & 
  S1=union(S1_6859,{v_6857}) & S=union(S1_6769,
  {v_6767})))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                    S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{531,530}] * 
                    y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&
                    (([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_227,n_228,Anon_32,S3,Anon_33,
                                S4: x'::dll<Anon_32,m_227,S3>@M[Orig][LHSCase]@ rem br[{531,530}] * 
                                y'::dll<Anon_33,n_228,S4>@M[Orig][LHSCase]@ rem br[{531,530}]&
                                (([m=m_227][n=n_228]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                  S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{531,530}] * 
                  y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{531,530}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(Anon_6943,m_6944,S3_6945,Anon_6946,
                              n_6947,
                              S4_6948: x'::dll<Anon_6943,m_6944,S3_6945>@M[Orig][LHSCase]@ rem br[{531,530}] * 
                              y'::dll<Anon_6946,n_6947,S4_6948>@M[Orig][LHSCase]@ rem br[{531,530}]&
                              (
                              ([m=m_6944 & 0<=m][n=n_6947 & 0<=n][S1=S4_6948]
                               [S2=S3_6945][y=x'][x=y'][Anon_6943=Anon_31]
                               [Anon_6946=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (555,6)  (243,13)  (243,4)  (354,4)  (354,11)  (364,6)  (364,13)  (363,6)  (363,6)  (361,6)  (361,13)  (360,8)  (359,27)  (359,14)  (359,9)  (358,10)  (358,4)  (357,8)  (357,12)  (357,4)  (357,4) )

Total verification time: 10.81 second(s)
	Time spent in main process: 0.89 second(s)
	Time spent in child processes: 9.92 second(s)
