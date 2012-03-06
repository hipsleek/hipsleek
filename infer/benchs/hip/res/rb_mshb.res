/usr/local/bin/mona

Processing file "rb_mshb.ss"
Parsing rb_mshb.ss ...
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

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure del_6r_1$node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_6r_1$node~node~node~int SUCCESS

Checking procedure del_5r_1$node~node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_5r_1$node~node~node~node~int SUCCESS

Checking procedure remove_min_1$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure remove_min_1$node SUCCESS

Checking procedure del_1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_1$node~int SUCCESS

Checking procedure del_3$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL3(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL3]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                    S3](ex)EXISTS(ha_283,ha_284,flted_133_280,flted_133_281,
                    flted_133_282: a::rb1<na,flted_133_282,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    b::rb1<nb,flted_133_281,ha_283,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    c::rb1<nc,flted_133_280,ha_284,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                    (
                    ([flted_133_282=0][flted_133_281=0][flted_133_280=0]
                     [ha=ha_284 & ha=ha_283 & 1<=ha_284]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::
                                EXISTS(flted_134_277,flted_134_278,
                                flted_134_279,
                                S4: res::rb1<flted_134_279,flted_134_278,flted_134_277,S4>@M[Orig][LHSCase]@ rem br[{587}]&
                                (
                                ([flted_134_279=2+na+nb+nc][flted_134_278=0]
                                 [1!=flted_134_277 & -1+flted_134_277=ha]
                                 [S4!=() & DEL3(S1,S2,S3,S4)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                  S3](ex)a::rb1<na,flted_133_282,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  b::rb1<nb,flted_133_281,ha_283,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  c::rb1<nc,flted_133_280,ha_284,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                  (
                  ([ha_283=ha & ha_283=ha_284 & 1<=ha_283][0=flted_133_282]
                   [0=flted_133_281][0=flted_133_280]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 14::
                              EXISTS(flted_134_11562,flted_134_11563,
                              flted_134_11564,
                              S4_11565: res::rb1<flted_134_11564,flted_134_11563,flted_134_11562,S4_11565>@M[Orig][LHSCase]@ rem br[{587}]&
                              (
                              ([S4_11565!=() & S4_11565=union(S1,S2,S3,{0},
                                 {0})]
                               [null!=res]
                               [1!=flted_134_11562 & 1<=ha & -1+
                                 flted_134_11562=ha]
                               [0=flted_134_11563]
                               [flted_134_11564=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=ha_284]
                               [0<=flted_133_280 & flted_133_280<=1]
                               [1<=ha_283]
                               [0<=flted_133_281 & flted_133_281<=1]
                               [0<=flted_133_282 & flted_133_282<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_11485:exists(S2_11493:exists(S1_11489:exists(S1_11459:exists(S2_11464:exists(v_11454:v_11485=0 & 
  S2_11464=union(S1_11489,S2_11493,{v_11485}) & v_11454=0 & S1_11459=S1 & 
  S3=S2_11493 & S2=S1_11489 & S4=union(S1_11459,S2_11464,
  {v_11454})))))))) --> DEL3(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! REL :  DEL3R(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL3R]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                    S3](ex)EXISTS(ha_254,ha_255,flted_151_251,flted_151_252,
                    flted_151_253: a::rb1<na,flted_151_253,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    b::rb1<nb,flted_151_252,ha_254,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    c::rb1<nc,flted_151_251,ha_255,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                    (
                    ([flted_151_253=0][flted_151_252=0][flted_151_251=0]
                     [ha=ha_255 & ha=ha_254 & 1<=ha_255]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::
                                EXISTS(flted_152_248,flted_152_249,
                                flted_152_250,
                                S4: res::rb1<flted_152_250,flted_152_249,flted_152_248,S4>@M[Orig][LHSCase]@ rem br[{587}]&
                                (
                                ([flted_152_250=2+na+nb+nc][flted_152_249=0]
                                 [1!=flted_152_248 & -1+flted_152_248=ha]
                                 [S4!=() & DEL3R(S1,S2,S3,S4)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                  S3](ex)a::rb1<na,flted_151_253,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  b::rb1<nb,flted_151_252,ha_254,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  c::rb1<nc,flted_151_251,ha_255,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                  (
                  ([ha_254=ha & ha_254=ha_255 & 1<=ha_254][0=flted_151_253]
                   [0=flted_151_252][0=flted_151_251]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 17::
                              EXISTS(flted_152_11724,flted_152_11725,
                              flted_152_11726,
                              S4_11727: res::rb1<flted_152_11726,flted_152_11725,flted_152_11724,S4_11727>@M[Orig][LHSCase]@ rem br[{587}]&
                              (
                              ([S4_11727!=() & S4_11727=union(S1,S2,{0},S3,
                                 {0})]
                               [null!=res]
                               [1!=flted_152_11724 & 1<=ha & -1+
                                 flted_152_11724=ha]
                               [0=flted_152_11725]
                               [flted_152_11726=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=ha_255]
                               [0<=flted_151_251 & flted_151_251<=1]
                               [1<=ha_254]
                               [0<=flted_151_252 & flted_151_252<=1]
                               [0<=flted_151_253 & flted_151_253<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_11647:exists(S2_11655:exists(S1_11651:exists(S1_11621:exists(S2_11626:exists(v_11616:v_11647=0 & 
  S1_11621=union(S1_11651,S2_11655,{v_11647}) & v_11616=0 & S3=S2_11626 & 
  S2=S2_11655 & S1=S1_11651 & S4=union(S1_11621,S2_11626,
  {v_11616})))))))) --> DEL3R(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL4(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL4]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                    S3](ex)EXISTS(ha_341,ha_342,flted_93_338,flted_93_339,
                    flted_93_340: a::rb1<na,flted_93_340,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    b::rb1<nb,flted_93_339,ha_341,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    c::rb1<nc,flted_93_338,ha_342,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                    (
                    ([flted_93_340=0][flted_93_339=0][flted_93_338=0]
                     [ha=ha_342 & ha=ha_341 & 1<=ha_342]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_94_335,flted_94_336,
                                flted_94_337,
                                S4: res::rb1<flted_94_337,flted_94_336,flted_94_335,S4>@M[Orig][LHSCase]@ rem br[{587}]&
                                (
                                ([flted_94_337=2+na+nb+nc][flted_94_336=0]
                                 [1!=flted_94_335 & -1+flted_94_335=ha]
                                 [S4!=() & DEL4(S1,S2,S3,S4)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                  S3](ex)a::rb1<na,flted_93_340,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  b::rb1<nb,flted_93_339,ha_341,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  c::rb1<nc,flted_93_338,ha_342,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                  (
                  ([ha_341=ha & ha_341=ha_342 & 1<=ha_341][0=flted_93_340]
                   [0=flted_93_339][0=flted_93_338]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(flted_94_11886,flted_94_11887,
                              flted_94_11888,
                              S4_11889: res::rb1<flted_94_11888,flted_94_11887,flted_94_11886,S4_11889>@M[Orig][LHSCase]@ rem br[{587}]&
                              (
                              ([S4_11889!=() & S4_11889=union(S1,S2,S3,{0},
                                 {0})]
                               [null!=res]
                               [1!=flted_94_11886 & 1<=ha & -1+
                                 flted_94_11886=ha]
                               [0=flted_94_11887]
                               [flted_94_11888=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=ha_342][0<=flted_93_338 & flted_93_338<=1]
                               [1<=ha_341][0<=flted_93_339 & flted_93_339<=1]
                               [0<=flted_93_340 & flted_93_340<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_11809:exists(S2_11817:exists(S1_11813:exists(S1_11783:exists(S2_11788:exists(v_11778:v_11809=0 & 
  S2_11788=union(S1_11813,S2_11817,{v_11809}) & v_11778=0 & S1_11783=S1 & 
  S3=S2_11817 & S2=S1_11813 & S4=union(S1_11783,S2_11788,
  {v_11778})))))))) --> DEL4(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! REL :  DEL4R(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL4R]
              EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                    S3](ex)EXISTS(ha_312,ha_313,flted_111_309,flted_111_310,
                    flted_111_311: a::rb1<na,flted_111_311,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    b::rb1<nb,flted_111_310,ha_312,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                    c::rb1<nc,flted_111_309,ha_313,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                    (
                    ([flted_111_311=0][flted_111_310=0][flted_111_309=0]
                     [ha=ha_313 & ha=ha_312 & 1<=ha_313]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(flted_112_306,flted_112_307,
                                flted_112_308,
                                S4: res::rb1<flted_112_308,flted_112_307,flted_112_306,S4>@M[Orig][LHSCase]@ rem br[{587}]&
                                (
                                ([flted_112_308=2+na+nb+nc][flted_112_307=0]
                                 [1!=flted_112_306 & -1+flted_112_306=ha]
                                 [S4!=() & DEL4R(S1,S2,S3,S4)][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; S1; nb; S2; nc; ha; 
                  S3](ex)a::rb1<na,flted_111_311,ha,S1>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  b::rb1<nb,flted_111_310,ha_312,S2>@M[Orig][LHSCase]@ rem br[{589,587}] * 
                  c::rb1<nc,flted_111_309,ha_313,S3>@M[Orig][LHSCase]@ rem br[{589,587}]&
                  (
                  ([ha_312=ha & ha_312=ha_313 & 1<=ha_312][0=flted_111_311]
                   [0=flted_111_310][0=flted_111_309]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(flted_112_12048,flted_112_12049,
                              flted_112_12050,
                              S4_12051: res::rb1<flted_112_12050,flted_112_12049,flted_112_12048,S4_12051>@M[Orig][LHSCase]@ rem br[{587}]&
                              (
                              ([S4_12051!=() & S4_12051=union(S1,S2,{0},S3,
                                 {0})]
                               [null!=res]
                               [1!=flted_112_12048 & 1<=ha & -1+
                                 flted_112_12048=ha]
                               [0=flted_112_12049]
                               [flted_112_12050=2+na+nb+nc & 0<=na & 0<=nc & 
                                 0<=nb]
                               [1<=ha_313]
                               [0<=flted_111_309 & flted_111_309<=1]
                               [1<=ha_312]
                               [0<=flted_111_310 & flted_111_310<=1]
                               [0<=flted_111_311 & flted_111_311<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_11971:exists(S2_11979:exists(S1_11975:exists(S1_11945:exists(S2_11950:exists(v_11940:v_11971=0 & 
  S1_11945=union(S1_11975,S2_11979,{v_11971}) & v_11940=0 & S3=S2_11950 & 
  S2=S2_11979 & S1=S1_11975 & S4=union(S1_11945,S2_11950,
  {v_11940})))))))) --> DEL4R(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure insert_1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INS(S1,S,v)
!!! POST:  S= & S1={v} & forall(_x:_x <notin> S1  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; Anon_17; bh; 
                    S](ex)x::rb1<n,Anon_17,bh,S>@M[Orig][LHSCase]@ rem br[{589,588,587}]&
                    (([true][1<=bh][Anon_17<=1 & 0<=Anon_17]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 69::
                                EXISTS(flted_414_172,Anon_18,bh1,
                                S1: res::rb1<flted_414_172,Anon_18,bh1,S1>@M[Orig][LHSCase]@ rem br[{588,587}]&
                                (
                                ([-1+flted_414_172=n][null!=res]
                                 [bh1<=bh & bh<=bh1][S1!=() & INS(S1,S,v)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; Anon_17; bh; 
                  S](ex)x::rb1<n,Anon_17,bh,S>@M[Orig][LHSCase]@ rem br[{589,588,587}]&
                  (([1<=bh][Anon_17<=1 & 0<=Anon_17]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 69::
                              EXISTS(flted_414_13573,Anon_13574,bh1_13575,
                              S1_13576: res::rb1<flted_414_13573,Anon_13574,bh1_13575,S1_13576>@M[Orig][LHSCase]@ rem br[{588,587}]&
                              (
                              ([forall(_x:_x <notin> S1_13576  | _x=v) & 
                                 S1_13576!=() & S1_13576={v}]
                               [S=][bh1_13575<=bh & 1<=bh & bh<=bh1_13575]
                               [null!=res][-1+flted_414_13573=n & 0<=n]
                               [Anon_17<=1 & 0<=Anon_17]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_13528:exists(S2_13532:exists(v_13524:S1_13528= & S2_13532= & 
  v_13524=v & S= & S1=union(S1_13528,S2_13532,{v_13524}))))) --> INS(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert_1$node~int SUCCESS

Termination checking result:


304 false contexts at: ( (518,4)  (515,5)  (511,7)  (508,8)  (508,15)  (507,12)  (507,51)  (507,37)  (507,29)  (507,8)  (507,8)  (503,8)  (503,15)  (502,24)  (502,8)  (501,23)  (501,8)  (501,8)  (499,20)  (499,11)  (499,7)  (494,7)  (494,14)  (493,11)  (493,68)  (493,48)  (493,29)  (493,21)  (493,7)  (493,7)  (489,7)  (489,14)  (488,23)  (488,7)  (487,22)  (487,7)  (487,7)  (485,19)  (485,10)  (485,6)  (472,4)  (469,5)  (465,7)  (461,8)  (461,15)  (460,12)  (460,73)  (460,53)  (460,34)  (460,21)  (460,8)  (460,8)  (456,8)  (456,15)  (455,24)  (455,8)  (454,23)  (454,8)  (454,8)  (452,20)  (452,11)  (452,7)  (445,7)  (445,14)  (444,11)  (444,54)  (444,40)  (444,27)  (444,7)  (444,7)  (440,7)  (440,14)  (439,23)  (439,7)  (438,22)  (438,7)  (438,7)  (436,19)  (436,10)  (436,6)  (377,4)  (399,12)  (399,57)  (399,42)  (399,28)  (399,20)  (399,8)  (396,13)  (396,83)  (396,68)  (396,48)  (396,29)  (396,21)  (396,9)  (393,14)  (393,44)  (393,30)  (393,22)  (393,10)  (391,14)  (391,44)  (391,30)  (391,22)  (391,10)  (390,24)  (390,13)  (390,13)  (390,9)  (388,23)  (388,12)  (388,8)  (387,22)  (387,11)  (387,7)  (383,12)  (383,42)  (383,28)  (383,20)  (383,8)  (382,11)  (382,11)  (382,7)  (380,19)  (380,10)  (380,6)  (379,20)  (379,9)  (379,5)  (377,8)  (377,24)  (377,21)  (348,4)  (368,12)  (368,57)  (368,48)  (368,34)  (368,21)  (368,8)  (366,13)  (366,83)  (366,74)  (366,54)  (366,35)  (366,22)  (366,9)  (364,14)  (364,50)  (364,36)  (364,23)  (364,10)  (362,14)  (362,50)  (362,36)  (362,23)  (362,10)  (361,24)  (361,13)  (361,13)  (361,9)  (360,23)  (360,12)  (360,8)  (359,22)  (359,11)  (359,7)  (354,12)  (354,48)  (354,34)  (354,21)  (354,8)  (353,11)  (353,11)  (353,7)  (351,19)  (351,10)  (351,6)  (350,20)  (350,9)  (350,5)  (348,8)  (348,25)  (348,22)  (314,4)  (334,12)  (334,57)  (334,48)  (334,34)  (334,21)  (334,8)  (332,13)  (332,83)  (332,74)  (332,54)  (332,35)  (332,22)  (332,9)  (330,14)  (330,50)  (330,36)  (330,23)  (330,10)  (328,14)  (328,50)  (328,36)  (328,23)  (328,10)  (327,24)  (327,13)  (327,13)  (327,9)  (326,23)  (326,12)  (326,8)  (325,22)  (325,11)  (325,7)  (321,12)  (321,48)  (321,34)  (321,21)  (321,8)  (320,11)  (320,11)  (320,7)  (318,19)  (318,10)  (318,6)  (316,20)  (316,9)  (316,5)  (314,8)  (314,25)  (314,22)  (286,3)  (286,10)  (283,4)  (283,11)  (277,6)  (277,13)  (276,10)  (276,55)  (276,40)  (276,26)  (276,18)  (276,6)  (276,6)  (271,7)  (271,14)  (270,11)  (270,81)  (270,66)  (270,46)  (270,27)  (270,19)  (270,7)  (270,7)  (266,8)  (266,15)  (265,12)  (265,42)  (265,28)  (265,20)  (265,8)  (265,8)  (261,8)  (261,15)  (260,12)  (260,42)  (260,28)  (260,20)  (260,8)  (260,8)  (258,22)  (258,11)  (258,11)  (258,7)  (257,21)  (257,10)  (257,6)  (255,20)  (255,9)  (255,5)  (251,6)  (251,13)  (248,48)  (248,55)  (247,10)  (247,40)  (247,26)  (247,18)  (247,6)  (247,6)  (245,9)  (245,9)  (245,5)  (243,17)  (243,8)  (243,4)  (241,18)  (241,7)  (241,3)  (239,6)  (239,22)  (239,19) )

Total verification time: 10.99 second(s)
	Time spent in main process: 4.74 second(s)
	Time spent in child processes: 6.25 second(s)
