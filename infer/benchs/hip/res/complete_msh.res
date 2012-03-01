
Processing file "complete_msh.ss"
Parsing complete_msh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node2... 
!!! REL :  COUNT(res)
!!! POST:  res>=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [COUNT]
              EBase exists (Expl)(Impl)[h; 
                    nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(h_63,
                                nmin_64: t::complete<h_63,nmin_64>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([COUNT(res)]
                                 [h_63=h & nmin=nmin_64 & nmin_64<=h_63 & 
                                   0<=nmin_64]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[h; 
                  nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(h_1042,
                              nmin_1043: t::complete<h_1042,nmin_1043>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([0<=res]
                               [nmin=nmin_1043 & h=h_1042 & nmin<=h & 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0) --> COUNT(res),
 (COUNT(cleft_65') & COUNT(cright_66') & 1+cleft_65'+
  cright_66'=res) --> COUNT(res),
 (COUNT(cright_66') & COUNT(cleft_65') & 1+cleft_65'+
  cright_66'=res) --> COUNT(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure maxim$int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&(())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                    EAssume 1::
                      
                      true&(([res=a & b<=res]))&{FLOW,(20,21)=__norm}
                      or true&(([res=b & (1+a)<=res]))&{FLOW,(20,21)=__norm}
                      )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure maxim$int~int SUCCESS

Checking procedure height$node2... 
!!! REL :  HGT(res,h)
!!! POST:  h>=0 & h=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [HGT]
              EBase exists (Expl)(Impl)[h; 
                    nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(h_61,
                                nmin_62: t::complete<h_61,nmin_62>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([h_61=h & nmin=nmin_62 & 0<=nmin_62 & 
                                   nmin_62<=h_61 & HGT(res,h)]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[h; 
                  nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(h_1402,
                              nmin_1403: t::complete<h_1402,nmin_1403>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([nmin=nmin_1403 & res=h & res=h_1402 & 0<=h & 
                                 0<=nmin & nmin_1403<=h_1402]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & h=0) --> HGT(res,h),
 (exists(nmin_62:exists(nmin:HGT(v_int_97_1201,h_1121) & 
  HGT(v_int_97_1184,h_1143) & (1+v_int_97_1184)<=res & -2+h=h_1143 & 1+
  v_int_97_1201=res & -1+h_1121=h_1143 & 
  exists(nmin2_1102:exists(nmin1_1100:1<=nmin1_1100 & nmin2_1102<=h_1143 & 
  (-1+nmin=nmin2_1102 & -1+nmin_62=nmin2_1102 & 0<=nmin2_1102 & 
  nmin2_1102<=nmin1_1100 & (-1+nmin1_1100)<=h_1143 | nmin_62=nmin & 1+
  nmin1_1100=nmin & nmin<=nmin2_1102)))))) --> HGT(res,h),
 (exists(nmin_62:exists(nmin:HGT(v_int_97_1186,h_1121) & 
  HGT(v_int_97_1250,h_1143) & (2+v_int_97_1186)<=res & -2+h=h_1143 & 1+
  v_int_97_1250=res & -1+h_1121=h_1143 & 
  exists(nmin2_1102:exists(nmin1_1100:1<=nmin1_1100 & nmin2_1102<=h_1143 & 
  (-1+nmin=nmin2_1102 & -1+nmin_62=nmin2_1102 & 0<=nmin2_1102 & 
  nmin2_1102<=nmin1_1100 & (-1+nmin1_1100)<=h_1143 | nmin_62=nmin & 1+
  nmin1_1100=nmin & nmin<=nmin2_1102)))))) --> HGT(res,h),
 (exists(nmin_62:exists(nmin:HGT(v_int_97_1188,h_1143) & 
  HGT(v_int_97_1299,h_1121) & (1+v_int_97_1188)<=res & 1+v_int_97_1299=res & 
  -1+h=h_1143 & h_1121=h_1143 & (exists(nmin1_1115:nmin_62=nmin & 1<=nmin & 
  (-1+nmin)<=nmin1_1115 & nmin1_1115<=h_1143) | 
  exists(nmin2_1117:nmin_62=nmin & 1<=nmin & nmin<=nmin2_1117 & 
  nmin2_1117<=h_1143))))) --> HGT(res,h),
 (exists(nmin_62:exists(nmin:HGT(v_int_97_1348,h_1143) & 
  HGT(v_int_97_1190,h_1121) & (2+v_int_97_1190)<=res & 1+v_int_97_1348=res & 
  -1+h=h_1143 & h_1121=h_1143 & (exists(nmin1_1115:nmin_62=nmin & 1<=nmin & 
  (-1+nmin)<=nmin1_1115 & nmin1_1115<=h_1143) | 
  exists(nmin2_1117:nmin_62=nmin & 1<=nmin & nmin<=nmin2_1117 & 
  nmin2_1117<=h_1143))))) --> HGT(res,h),
 (h=0 & res=0) --> HGT(res,h)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node2 SUCCESS

Checking procedure insert$node2~int... 
Procedure insert$node2~int SUCCESS

Checking procedure is_perfect$node2... 
!!! REL :  PERFECT(nmin,h,res)
!!! POST:  res>=0 & (res+nmin)>=1 & 1>=res & (res+h)>=(1+nmin)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PERFECT]
              EBase exists (Expl)(Impl)[h; 
                    nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(h_51,
                                nmin_52: t::complete<h_51,nmin_52>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([h=h_51 & nmin=nmin_52 & 0<=nmin_52 & 
                                   nmin_52<=h_51 & PERFECT(nmin,h,res)]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[h; 
                  nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              EXISTS(h_2565,
                              nmin_2566: t::complete<h_2565,nmin_2566>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([nmin=nmin_2566 & h=h_2565 & nmin<=(-1+h+
                                 res) & 0<=nmin & nmin_2566<=h_2565 & 
                                 1<=(nmin+res) & res<=1 & 0<=res]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=1 & h=0 & nmin=0) --> PERFECT(nmin,h,res),
 (nmin=0 & h=0 & res=1) --> PERFECT(nmin,h,res),
 (exists(nmin_52:res=0 & exists(nmin1_2434:1<=nmin1_2434 & 
  exists(nmin2_2317:(nmin_52=nmin & 1+nmin2_2317=nmin & 1<=nmin & (-1+
  nmin)<=nmin1_2434 & (1+nmin1_2434)<=h | nmin_52=nmin & 1+nmin1_2434=nmin & 
  nmin<=nmin2_2317) & (2+nmin2_2317)<=h)))) --> PERFECT(nmin,h,res),
 (exists(nmin_52:PERFECT(nmin_2386,h_2385,1) & 
  PERFECT(nmin_2408,h_2407,v_int_198_601') & v_int_198_601'=res & 
  (nmin_52=nmin & 1+nmin_2408=nmin & 1<=nmin & (-1+nmin)<=nmin_2386 & (1+
  nmin_2386)<=h | nmin_52=nmin & 1+nmin_2386=nmin & 1<=nmin & 
  nmin<=nmin_2408 & (1+nmin_2408)<=h) & 1+h_2385=h & 1+
  h_2407=h)) --> PERFECT(nmin,h,res),
 (exists(nmin_52:exists(h_2358:exists(nmin1_2521:exists(flted_26_2326:exists(h_51:exists(flted_26_2327:PERFECT(nmin_2386,h_2385,v_int_197_2518) & 
  res=0 & exists(nmin1_2330:1+h_2358=h & 1+h_2385=h & 1+flted_26_2326=h & 
  h_51=h & 1+flted_26_2327=h & exists(nmin2_2332:nmin1_2521=nmin_2386 & 
  nmin1_2330=nmin_2386 & (nmin_52=nmin & 1+nmin2_2332=nmin & 1<=nmin & (-1+
  nmin)<=nmin_2386 & (1+nmin_2386)<=h & 2<=v_int_197_2518 | nmin_52=nmin & 1+
  nmin_2386=nmin & 1<=nmin & nmin<=nmin2_2332 & (1+nmin2_2332)<=h & 
  v_int_197_2518<=0 | nmin_52=nmin & 1+nmin2_2332=nmin & 1<=nmin & (-1+
  nmin)<=nmin_2386 & (1+nmin_2386)<=h & v_int_197_2518<=0 | nmin_52=nmin & 1+
  nmin_2386=nmin & 1<=nmin & nmin<=nmin2_2332 & (1+nmin2_2332)<=h & 
  2<=v_int_197_2518)))))))))) --> PERFECT(nmin,h,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_perfect$node2 SUCCESS

Checking procedure minim$int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&(())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 3::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                    EAssume 3::
                      
                      true&(([res=b & res<=a]))&{FLOW,(20,21)=__norm}
                      or true&(([res=a & (1+res)<=b]))&{FLOW,(20,21)=__norm}
                      )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure minim$int~int SUCCESS

Checking procedure min_height$node2... 
!!! REL :  MHGT(res,nmin)
!!! POST:  nmin>=0 & nmin=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MHGT]
              EBase exists (Expl)(Impl)[h; 
                    nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(h_57,
                                nmin_58: t::complete<h_57,nmin_58>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([h_57=h & nmin=nmin_58 & 0<=nmin_58 & 
                                   nmin_58<=h_57 & MHGT(res,nmin)]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[h; 
                  nmin](ex)t::complete<h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(h_2925,
                              nmin_2926: t::complete<h_2925,nmin_2926>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([res=nmin & res=nmin_2926 & h=h_2925 & 
                                 nmin_2926<=h_2925 & 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & nmin=0) --> MHGT(res,nmin),
 (exists(nmin_58:MHGT(v_int_112_2707,nmin_2645) & 
  MHGT(v_int_112_2724,nmin_2667) & (-1+res)<=v_int_112_2707 & 1+
  v_int_112_2724=res & 1<=nmin_2645 & exists(flted_25_2620:(nmin_58=nmin & 1+
  nmin_2667=nmin & 1<=nmin & (-1+nmin)<=nmin_2645 & 
  nmin_2645<=flted_25_2620 | nmin_58=nmin & 1+nmin_2645=nmin & 
  nmin<=nmin_2667) & (1+nmin_2667)<=flted_25_2620))) --> MHGT(res,nmin),
 (exists(nmin_58:MHGT(v_int_112_2773,nmin_2645) & 
  MHGT(v_int_112_2709,nmin_2667) & res<=v_int_112_2709 & 1+
  v_int_112_2773=res & 1<=nmin_2645 & exists(flted_25_2620:(nmin_58=nmin & 1+
  nmin_2667=nmin & 1<=nmin & (-1+nmin)<=nmin_2645 & 
  nmin_2645<=flted_25_2620 | nmin_58=nmin & 1+nmin_2645=nmin & 
  nmin<=nmin_2667) & (1+nmin_2667)<=flted_25_2620))) --> MHGT(res,nmin),
 (exists(nmin_58:MHGT(v_int_112_2822,nmin_2667) & 
  MHGT(v_int_112_2711,nmin_2645) & (-1+res)<=v_int_112_2711 & 1+
  v_int_112_2822=res & (exists(h:nmin_58=nmin & 1+nmin_2667=nmin & 1<=nmin & 
  (-1+nmin)<=nmin_2645 & (1+nmin_2645)<=h) | exists(h:nmin_58=nmin & 1+
  nmin_2645=nmin & 1<=nmin & nmin<=nmin_2667 & (1+
  nmin_2667)<=h)))) --> MHGT(res,nmin),
 (exists(nmin_58:MHGT(v_int_112_2713,nmin_2667) & 
  MHGT(v_int_112_2871,nmin_2645) & res<=v_int_112_2713 & 1+
  v_int_112_2871=res & (exists(h:nmin_58=nmin & 1+nmin_2667=nmin & 1<=nmin & 
  (-1+nmin)<=nmin_2645 & (1+nmin_2645)<=h) | exists(h:nmin_58=nmin & 1+
  nmin_2645=nmin & 1<=nmin & nmin<=nmin_2667 & (1+
  nmin_2667)<=h)))) --> MHGT(res,nmin),
 (nmin=0 & res=0) --> MHGT(res,nmin)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:

Stop Omega... 2490 invocations 
30 false contexts at: ( (170,12)  (169,12)  (168,12)  (167,18)  (167,12)  (167,12)  (156,10)  (155,10)  (154,10)  (153,16)  (153,10)  (153,10)  (149,8)  (148,8)  (147,8)  (146,14)  (146,8)  (146,8)  (164,12)  (163,12)  (162,12)  (161,18)  (161,12)  (161,12)  (142,2)  (141,25)  (141,19)  (141,6)  (141,2)  (141,2) )

Total verification time: 2.37 second(s)
	Time spent in main process: 0.93 second(s)
	Time spent in child processes: 1.44 second(s)
