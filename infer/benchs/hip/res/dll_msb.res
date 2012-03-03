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
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{486}] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&(
                    ([0!=m][null!=x][S1!=()][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                EXISTS(q_194,t,
                                S: x::dll<q_194,t,S>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([t=m+n][APP2(S,S1,S2)][q=q_194]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase]@ rem br[{486}] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              EXISTS(q_1938,t_1939,
                              S_1940: x::dll<q_1938,t_1939,S_1940>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([S_1940=union(S1,S2)][q=q_1938]
                               [t_1939=m+n & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_1830:exists(v_1675:exists(v_1828:exists(S1_1677:S1!=() & S2= & 
  S=union(S1_1830,{v_1828}) & S1=union(S1_1677,{v_1675}) & S1_1830=S2 & 
  v_1675=v_1828 & S1_1677=))))) --> APP2(S,S1,S2),
 (exists(flted_12_1674:exists(m:exists(p_1672:exists(q_194:exists(q:exists(self_1735:exists(p_1734:exists(p:exists(v_1788:exists(S1_1790:exists(n:exists(q_1738:exists(q_1789:exists(q_1775:exists(x:exists(flted_12_1736:exists(q_1676:exists(y:exists(self_1673:exists(v_bool_188_1312':exists(v_bool_186_1317':exists(t:exists(S1_1776:exists(v_1774:exists(S1_1677:exists(v_1675:exists(S1_1739:exists(v_1737:S1_1776=union(S1_1790,
  {v_1788}) & S1_1677= & (flted_12_1674=0 & m=1 & p_1672=q & q_194=q & 
  self_1735=y & p_1734=p & v_1774=v_1675 & v_1788=v_1737 & S1_1739=S1_1790 & 
  1+n=t & q_1738=q_1789 & q_1775=y & x=self_1673 & 2+flted_12_1736=t & 
  q_1676=null & t<=0 & y!=null & self_1673!=null & 1<=v_bool_188_1312' & 
  1<=v_bool_186_1317' | flted_12_1674=0 & m=1 & p_1672=q & q_194=q & 
  self_1735=y & p_1734=p & v_1774=v_1675 & v_1788=v_1737 & S1_1739=S1_1790 & 
  1+n=t & q_1738=q_1789 & q_1775=y & x=self_1673 & 2+flted_12_1736=t & 
  q_1676=null & y!=null & self_1673!=null & 1<=v_bool_188_1312' & 
  1<=v_bool_186_1317' & 2<=t) & S2!=() & S=union(S1_1776,{v_1774}) & 
  S1=union(S1_1677,{v_1675}) & S2=union(S1_1739,{v_1737}) & 
  S1!=()))))))))))))))))))))))))))))) --> APP2(S,S1,S2),
 (exists(S1_1677:exists(v_1675:exists(S1_1830:exists(v_1828:S1_1677= & 
  v_1675=v_1828 & S2=S1_1830 & S1=union(S1_1677,{v_1675}) & S=union(S1_1830,
  {v_1828}) & S2= & S1!=()))))) --> APP2(S,S1,S2),
 (exists(S1_1860:exists(v_1858:exists(S1_1677:exists(v_1675:S_1857!=() & 
  S1_1677!=() & S1_1677=S1_1748 & v_1675=v_1858 & S_1857=S1_1860 & 
  S2_1751=S2 & APP2(S_1857,S1_1748,S2_1751) & S1!=() & S=union(S1_1860,
  {v_1858}) & S1=union(S1_1677,{v_1675})))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure create_list$int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  m <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[Anon_74; n; 
                    S](ex)x::dll<Anon_74,n,S>@M[Orig][LHSCase]@ rem br[{487,486}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 117::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_75,Anon_76,
                                   m: res::node<m,Anon_75,Anon_76>@M[Orig][]&
                                   (([FGE(S,m) & (1+v)<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_74; n; 
                  S](ex)x::dll<Anon_74,n,S>@M[Orig][LHSCase]@ rem br[{487,486}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 117::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_2744,Anon_2745,
                                 m_2746: res::node<m_2746,Anon_2744,Anon_2745>@M[Orig][]&
                                 (
                                 ([(1+v)<=m_2746 & m_2746 <in> S ][res!=null]
                                  [0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(x:exists(res:exists(p_2651:exists(Anon_74:exists(Anon_75:exists(Anon_76:exists(q_2655:exists(self_2652:exists(flted_12_2653:exists(v_bool_530_801':exists(v:exists(v_node_534_794':exists(v_bool_533_800':exists(n:exists(S1_2656:exists(v_2654:(x=v_node_534_794' & 
  res=v_node_534_794' & p_2651=Anon_75 & Anon_74=Anon_75 & Anon_76=q_2655 & 
  m=v_2654 & self_2652=v_node_534_794' & 1+flted_12_2653=n & 
  v_bool_530_801'<=0 & (1+v)<=v_2654 & n<=-1 & v_node_534_794'!=null & 
  1<=v_bool_533_800' | x=v_node_534_794' & res=v_node_534_794' & 
  p_2651=Anon_75 & Anon_74=Anon_75 & Anon_76=q_2655 & m=v_2654 & 
  self_2652=v_node_534_794' & 1+flted_12_2653=n & v_bool_530_801'<=0 & (1+
  v)<=v_2654 & v_node_534_794'!=null & 1<=v_bool_533_800' & 1<=n) & S!=() & 
  S=union(S1_2656,{v_2654})))))))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2656:exists(v_2654:v_2654<=v & S1_2656=S_2682 & 
  m_2720=m & (1+v)<=m & FGE(S_2682,m_2720) & S=union(S1_2656,{v_2654}) & 
  S!=())))) --> FGE(S,m)]
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
              EBase exists (Expl)(Impl)[Anon_43; n; 
                    S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{486}]&
                    (([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::ref [x]
                                EXISTS(flted_213_190,flted_213_191,Anon_44,
                                Anon_45,S1,
                                S2: x'::dll<Anon_44,flted_213_191,S1>@M[Orig][LHSCase]@ rem br[{486}] * 
                                res::dll<Anon_45,flted_213_190,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (
                                ([1=flted_213_191][1+flted_213_190=n]
                                 [S1!=() & GN(S,S1,S2)][null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_43; n; 
                  S](ex)x::dll<Anon_43,n,S>@M[Orig][LHSCase]@ rem br[{486}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::ref [x]
                              EXISTS(flted_213_2853,flted_213_2854,Anon_2855,
                              Anon_2856,S1_2857,
                              S2_2858: x'::dll<Anon_2855,flted_213_2854,S1_2857>@M[Orig][LHSCase]@ rem br[{486}] * 
                              res::dll<Anon_2856,flted_213_2853,S2_2858>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([S1_2857!=() & union(S1_2857,S2_2858)=S]
                               [null!=x'][1+flted_213_2853=n & 0<=n]
                               [1=flted_213_2854]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(flted_213_191:exists(q_2801:exists(tmp_192':exists(res:exists(q_2781:exists(v_node_218_1273':exists(Anon_43:exists(p_2777:exists(self_2778:exists(x':exists(n:exists(next_217_2799:exists(prev_217_1271':exists(x:exists(flted_213_190:exists(next_216_1268':exists(Anon_44:exists(Anon_45:exists(flted_12_2779:exists(S1_2782:exists(v_2780:exists(S1_2802:exists(v_2800:S1_2802= & 
  (flted_213_191=1 & q_2801=next_216_1268' & tmp_192'=v_node_218_1273' & 
  res=v_node_218_1273' & q_2781=v_node_218_1273' & Anon_43=p_2777 & 
  self_2778=Anon_45 & x'=Anon_45 & -1+n=flted_12_2779 & v_2800=v_2780 & 
  S1_2782=S2 & next_217_2799=next_216_1268' & prev_217_1271'=Anon_44 & 
  x=Anon_45 & flted_213_190=flted_12_2779 & next_216_1268'=null & 
  Anon_44=null & flted_12_2779<=-2 & Anon_45!=null | flted_213_191=1 & 
  q_2801=next_216_1268' & tmp_192'=v_node_218_1273' & res=v_node_218_1273' & 
  q_2781=v_node_218_1273' & Anon_43=p_2777 & self_2778=Anon_45 & 
  x'=Anon_45 & -1+n=flted_12_2779 & v_2800=v_2780 & S1_2782=S2 & 
  next_217_2799=next_216_1268' & prev_217_1271'=Anon_44 & x=Anon_45 & 
  flted_213_190=flted_12_2779 & next_216_1268'=null & Anon_44=null & 
  Anon_45!=null & 0<=flted_12_2779) & S=union(S1_2782,{v_2780}) & 
  S1=union(S1_2802,{v_2800}) & S!=())))))))))))))))))))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[Anon_62; n; 
                    S](ex)x::dll<Anon_62,n,S>@M[Orig][LHSCase]@ rem br[{486}]&
                    (([2<=n][null!=x][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(flted_259_179,Anon_63,
                                S2: res::dll<Anon_63,flted_259_179,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([2+flted_259_179=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_62; n; 
                  S](ex)x::dll<Anon_62,n,S>@M[Orig][LHSCase]@ rem br[{486}]&(
                  ([S!=()][2<=n][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(flted_259_2953,Anon_2954,
                              S2_2955: res::dll<Anon_2954,flted_259_2953,S2_2955>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([2+flted_259_2953=n & 0<=n]
                               [S2_2955<subset> S ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_2930:exists(S1_2932:exists(S1_2889:exists(v_2887:S1_2889=union(S1_2932,
  {v_2930}) & S1_2889!=() & S2=S1_2932 & S!=() & S=union(S1_2889,
  {v_2887})))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INSERT(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{486}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(p_177,m,
                                S1: x::dll<p_177,m,S1>@M[Orig][LHSCase]@ rem br[{486}]&
                                (
                                ([-1+m=n][S1!=() & INSERT(S,S1,a)][p=p_177]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]@ rem br[{486}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              EXISTS(p_3120,m_3121,
                              S1_3122: x::dll<p_3120,m_3121,S1_3122>@M[Orig][LHSCase]@ rem br[{486}]&
                              (
                              ([S1_3122!=() & S1_3122=union(S,{a})][null!=x]
                               [p=p_3120][-1+m_3121=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3048:exists(v_3046:exists(S1_3034:exists(v_3032:exists(S1_2987:exists(v_2985:S1_3048= & 
  S1_3034=union(S1_3048,{v_3046}) & S1_2987= & v_2985=v_3032 & v_3046=a & 
  S1=union(S1_3034,{v_3032}) & S=union(S1_2987,{v_2985}) & 
  S!=()))))))) --> INSERT(S,S1,a),
 (exists(S1_3075:exists(v_3073:exists(S1_2987:exists(v_2985:S1_2987!=() & 
  S1_3072!=() & v_3073=v_2985 & S1_2987=S_3015 & S1_3072=S1_3075 & 
  INSERT(S_3015,S1_3072,a) & S!=() & S1=union(S1_3075,{v_3073}) & 
  S=union(S1_2987,{v_2985})))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
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

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; n; 
                    S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{487,486}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 82::
                                EXISTS(p_165,n_166,
                                S2: x::dll<p_165,n_166,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([TRAV(S1,S2)][p=p_165][n=n_166]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]@ rem br[{487,486}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 82::
                              EXISTS(p_4683,n_4684,
                              S2_4685: x::dll<p_4683,n_4684,S2_4685>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (([S1=S2_4685][n=n_4684 & 0<=n][p=p_4683]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_4643:exists(v_4641:exists(S1_4617:exists(v_4615:v_4641=v_4615 & 
  S1_4617=S1_4623 & S2_4640=S1_4643 & TRAV(S1_4623,S2_4640) & S1!=() & 
  S2=union(S1_4643,{v_4641}) & S1=union(S1_4617,
  {v_4615})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
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
              EBase exists (Expl)(Impl)[Anon_39; m; 
                    S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{486}]&
                    (([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 24::ref [x]
                                EXISTS(flted_117_197,Anon_40,
                                S2: x'::dll<Anon_40,flted_117_197,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([1+flted_117_197=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39; m; 
                  S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]@ rem br[{486}]&
                  (([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 24::ref [x]
                              EXISTS(flted_117_4877,Anon_4878,
                              S2_4879: x'::dll<Anon_4878,flted_117_4877,S2_4879>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([1+flted_117_4877=m & 0<=m]
                               [S2_4879<subset> S1 ]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4718:exists(v_4716:S1_4718= & S2= & S1=union(S1_4718,{v_4716}) & 
  S1!=()))) --> PF(S1,S2),
 (exists(q_4782:exists(q_4807:exists(Anon_39:exists(p_4713:exists(self_4779:exists(v_node_129_1357':exists(x:exists(res:exists(tmp_198':exists(v_4781:exists(S1_4783:exists(flted_12_4715:exists(m:exists(Anon_40:exists(self_4714:exists(q_4717:exists(flted_12_4780:exists(next_128_1356':exists(prev_126_1348':exists(v_bool_120_1358':exists(p_4778:exists(x':exists(flted_117_197:exists(S1_4808:exists(v_4806:exists(S1_4718:exists(v_4716:S1_4718!=() & 
  S1_4718=union(S1_4783,{v_4781}) & (q_4782=q_4807 & Anon_39=p_4713 & 
  self_4779=x' & v_node_129_1357'=p_4778 & x=p_4778 & res=p_4778 & 
  tmp_198'=p_4778 & v_4806=v_4781 & S1_4783=S1_4808 & 
  flted_12_4715=flted_117_197 & -1+m=flted_117_197 & 
  Anon_40=prev_126_1348' & self_4714=p_4778 & q_4717=x' & 1+
  flted_12_4780=flted_117_197 & next_128_1356'=null & prev_126_1348'=null & 
  flted_117_197<=-2 & v_bool_120_1358'<=0 & p_4778!=null & x'!=null | 
  q_4782=q_4807 & Anon_39=p_4713 & self_4779=x' & v_node_129_1357'=p_4778 & 
  x=p_4778 & res=p_4778 & tmp_198'=p_4778 & v_4806=v_4781 & 
  S1_4783=S1_4808 & flted_12_4715=flted_117_197 & -1+m=flted_117_197 & 
  Anon_40=prev_126_1348' & self_4714=p_4778 & q_4717=x' & 1+
  flted_12_4780=flted_117_197 & next_128_1356'=null & prev_126_1348'=null & 
  v_bool_120_1358'<=0 & p_4778!=null & x'!=null & 1<=flted_117_197) & 
  S1!=() & S2=union(S1_4808,{v_4806}) & S1=union(S1_4718,
  {v_4716}))))))))))))))))))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(S1,S)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_36; n; 
                    S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{487,486}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(v_199,n_200,Anon_37,q,Anon_38,
                                S1: x'::node<v_199,Anon_37,q>@M[Orig][] * 
                                q::dll<Anon_38,n_200,S1>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([PUF(S1,S)][v=v_199][n=n_200][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36; n; 
                  S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]@ rem br[{487,486}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(v_4992,n_4993,Anon_4994,q_4995,
                              Anon_4996,
                              S1_4997: x'::node<v_4992,Anon_4994,q_4995>@M[Orig][] * 
                              q_4995::dll<Anon_4996,n_4993,S1_4997>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([S=S1_4997][x'!=null][n=n_4993 & 0<=n]
                               [v=v_4992]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S=) --> PUF(S1,S),
 (exists(q_4919:exists(q_4937:exists(v:exists(v_199:exists(n:exists(Anon_38:exists(p_4915:exists(Anon_37:exists(Anon_36:exists(self_4916:exists(q:exists(x':exists(flted_12_4917:exists(v_bool_101_1379':exists(x:exists(tmp_201':exists(n_200:exists(S1_4920:exists(v_4918:exists(S1_4938:exists(v_4936:(q_4919=q_4937 & 
  v=v_199 & n=n_200 & v_4936=v_4918 & S1_4920=S1_4938 & Anon_38=Anon_36 & 
  p_4915=Anon_36 & Anon_37=Anon_36 & self_4916=x & q=x & x'=tmp_201' & 1+
  flted_12_4917=n_200 & n_200<=-1 & v_bool_101_1379'<=0 & x!=null & 
  tmp_201'!=null | q_4919=q_4937 & v=v_199 & n=n_200 & v_4936=v_4918 & 
  S1_4920=S1_4938 & Anon_38=Anon_36 & p_4915=Anon_36 & Anon_37=Anon_36 & 
  self_4916=x & q=x & x'=tmp_201' & 1+flted_12_4917=n_200 & 
  v_bool_101_1379'<=0 & x!=null & tmp_201'!=null & 1<=n_200) & S!=() & 
  S=union(S1_4920,{v_4918}) & S1=union(S1_4938,
  {v_4936}))))))))))))))))))))))) --> PUF(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_41; n; 
                    S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{487,486}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                EXISTS(n_193,Anon_42,
                                S2: x::dll<Anon_42,n_193,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([n=n_193]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_41; n; 
                  S1](ex)x::dll<Anon_41,n,S1>@M[Orig][LHSCase]@ rem br[{487,486}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              EXISTS(Anon_5003,n_5004,
                              S2_5005: x::dll<Anon_5003,n_5004,S2_5005>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([n=n_5004 & 0<=n][S1=S2_5005][res=x]
                               [Anon_5003=Anon_41]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(S,S2)
!!! POST:  S=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                    Anon_49; j; 
                    S](ex)EXISTS(x_184: x::node<v,Anon_46,t>@M[Orig][] * 
                    t::dll<x_184,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{487,486}] * 
                    y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{487,486}]&(
                    ([x=x_184 & x!=null][0<=Anon_47][true]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::ref [x]
                                EXISTS(v_185,y_186,j_187,Anon_50,Anon_51,
                                S2: x::node<v_185,Anon_50,y_186>@M[Orig][] * 
                                y::dll<Anon_51,j_187,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (
                                ([SN(S,S2)][v=v_185][y=y_186][j=j_187]
                                 [x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; Anon_46; t; Anon_47; Anon_48; 
                  Anon_49; j; S](ex)x::node<v,Anon_46,t>@M[Orig][] * 
                  t::dll<x_184,Anon_47,Anon_48>@M[Orig][LHSCase]@ rem br[{487,486}] * 
                  y::dll<Anon_49,j,S>@M[Orig][LHSCase]@ rem br[{487,486}]&(
                  ([x=x_184 & x!=null][0<=Anon_47]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::ref [x]
                              EXISTS(v_5510,y_5511,j_5512,Anon_5514,
                              S2_5515: y::dll<Anon_5514,j_5512,S2_5515>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([S=S2_5515][x!=null][j=j_5512 & 0<=j]
                               [y=y_5511][v=v_5510][0<=Anon_47]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S2= & S2=S) --> SN(S,S2),
 (S=S2 & S2=) --> SN(S,S2),
 (exists(q_5436:exists(q_5452:exists(Anon_50:exists(Anon_46:exists(x_5385:exists(x':exists(self_5433:exists(p_5432:exists(Anon_49:exists(j:exists(v:exists(v_185:exists(y_186:exists(x:exists(flted_12_5434:exists(v_bool_228_1245':exists(y:exists(Anon_51:exists(Anon_47:exists(j_187:exists(S1_5437:exists(v_5435:exists(S1_5453:exists(v_5451:(q_5436=q_5452 & 
  Anon_50=Anon_46 & x_5385=Anon_51 & x'=Anon_51 & self_5433=y & 
  p_5432=Anon_49 & v_5451=v_5435 & S1_5437=S1_5453 & j=j_187 & v=v_185 & 
  y_186=y & x=Anon_51 & 1+flted_12_5434=j_187 & j_187<=-1 & 
  v_bool_228_1245'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 | 
  q_5436=q_5452 & Anon_50=Anon_46 & x_5385=Anon_51 & x'=Anon_51 & 
  self_5433=y & p_5432=Anon_49 & v_5451=v_5435 & S1_5437=S1_5453 & j=j_187 & 
  v=v_185 & y_186=y & x=Anon_51 & 1+flted_12_5434=j_187 & 
  v_bool_228_1245'<=0 & y!=null & Anon_51!=null & 0<=Anon_47 & 1<=j_187) & 
  S!=() & S=union(S1_5437,{v_5435}) & S2=union(S1_5453,
  {v_5451})))))))))))))))))))))))))) --> SN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure splice$node~node SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                    S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{487,486}] * 
                    y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&
                    (([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_204,n_205,Anon_32,S3,Anon_33,
                                S4: x'::dll<Anon_32,m_204,S3>@M[Orig][LHSCase]@ rem br[{487,486}] * 
                                y'::dll<Anon_33,n_205,S4>@M[Orig][LHSCase]@ rem br[{487,486}]&
                                (([m=m_204][n=n_205]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                  S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase]@ rem br[{487,486}] * 
                  y::dll<Anon_31,m,S2>@M[Orig][LHSCase]@ rem br[{487,486}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(Anon_6114,m_6115,S3_6116,Anon_6117,
                              n_6118,
                              S4_6119: x'::dll<Anon_6114,m_6115,S3_6116>@M[Orig][LHSCase]@ rem br[{487,486}] * 
                              y'::dll<Anon_6117,n_6118,S4_6119>@M[Orig][LHSCase]@ rem br[{487,486}]&
                              (
                              ([m=m_6115 & 0<=m][n=n_6118 & 0<=n][S1=S4_6119]
                               [S2=S3_6116][y=x'][x=y'][Anon_6114=Anon_31]
                               [Anon_6117=Anon_30]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (555,6)  (243,13)  (243,4)  (354,4)  (354,11)  (364,6)  (364,13)  (363,6)  (363,6)  (361,6)  (361,13)  (360,8)  (359,27)  (359,14)  (359,9)  (358,10)  (358,4)  (357,8)  (357,12)  (357,4)  (357,4) )

Total verification time: 10.2 second(s)
	Time spent in main process: 1.1 second(s)
	Time spent in child processes: 9.1 second(s)
