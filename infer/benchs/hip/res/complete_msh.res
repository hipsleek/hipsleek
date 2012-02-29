
Processing file "complete_msh.ss"
Parsing complete_msh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node2... 
Procedure count$node2 SUCCESS

Checking procedure maxim$int~int... 
Procedure maxim$int~int SUCCESS

Checking procedure height$node2... 
!!! REL :  HGT(res,h)
!!! POST:  res>=0 & res=h
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
                              EXISTS(h_1303,
                              nmin_1304: t::complete<h_1303,nmin_1304>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([nmin=nmin_1304 & h=res & h=h_1303 & 0<=res & 
                                 0<=nmin & nmin_1304<=h_1303]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & h=0) --> HGT(res,h),
 (exists(nmin_62:exists(nmin:HGT(v_int_75_1188,h_1150) & 
  HGT(v_int_75_1189,h_1128) & -2+h=h_1150 & -1+h_1128=h_1150 & 
  exists(nmin1_1107:exists(nmin2_1109:1<=nmin1_1107 & nmin2_1109<=h_1150 & 
  (-1+res=v_int_75_1189 & nmin_62=nmin & 1+nmin2_1109=nmin & 1<=nmin & (-1+
  nmin)<=nmin1_1107 & v_int_75_1188<=v_int_75_1189 & (-1+
  nmin1_1107)<=h_1150 | -1+res=v_int_75_1188 & -1+nmin=nmin1_1107 & -1+
  nmin_62=nmin1_1107 & (1+v_int_75_1189)<=v_int_75_1188 & (1+
  nmin1_1107)<=nmin2_1109 | -1+res=v_int_75_1189 & -1+nmin=nmin1_1107 & -1+
  nmin_62=nmin1_1107 & v_int_75_1188<=v_int_75_1189 & (1+
  nmin1_1107)<=nmin2_1109 | -1+res=v_int_75_1188 & nmin_62=nmin & 1+
  nmin2_1109=nmin & 1<=nmin & (-1+nmin)<=nmin1_1107 & (1+
  v_int_75_1189)<=v_int_75_1188 & (-1+
  nmin1_1107)<=h_1150)))))) --> HGT(res,h),
 (exists(nmin_62:exists(nmin:HGT(v_int_75_1192,h_1150) & 
  HGT(v_int_75_1193,h_1128) & -1+h=h_1150 & h_1128=h_1150 & 
  (exists(nmin1_1122:-1+res=v_int_75_1193 & nmin_62=nmin & 1<=nmin & (-1+
  nmin)<=nmin1_1122 & v_int_75_1192<=v_int_75_1193 & nmin1_1122<=h_1150) | 
  -1+res=v_int_75_1192 & (1+v_int_75_1193)<=v_int_75_1192 & 
  exists(nmin2_1124:nmin_62=nmin & 1<=nmin & nmin<=nmin2_1124 & 
  nmin2_1124<=h_1150) | -1+res=v_int_75_1193 & 
  v_int_75_1192<=v_int_75_1193 & exists(nmin2_1124:nmin_62=nmin & 1<=nmin & 
  nmin<=nmin2_1124 & nmin2_1124<=h_1150) | exists(nmin1_1122:-1+
  res=v_int_75_1192 & nmin_62=nmin & 1<=nmin & (-1+nmin)<=nmin1_1122 & (1+
  v_int_75_1193)<=v_int_75_1192 & nmin1_1122<=h_1150))))) --> HGT(res,h),
 (h=0 & res=0) --> HGT(res,h)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node2 SUCCESS

Checking procedure insert$node2~int... 
Procedure insert$node2~int SUCCESS

Checking procedure is_perfect$node2... 
Procedure is_perfect$node2 SUCCESS

Checking procedure minim$int~int... 
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
                              EXISTS(h_2719,
                              nmin_2720: t::complete<h_2719,nmin_2720>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([res=nmin & res=nmin_2720 & h=h_2719 & 
                                 nmin_2720<=h_2719 & 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & nmin=0) --> MHGT(res,nmin),
 (exists(nmin_58:MHGT(v_int_90_2604,nmin_2567) & 
  MHGT(v_int_90_2605,nmin_2545) & 1<=nmin_2545 & exists(h:(-1+
  res=v_int_90_2604 & nmin_58=nmin & 1+nmin_2567=nmin & 1<=nmin & (-1+
  nmin)<=nmin_2545 & v_int_90_2604<=v_int_90_2605 & (1+nmin_2545)<=h | -1+
  res=v_int_90_2605 & nmin_58=nmin & 1+nmin_2545=nmin & nmin<=nmin_2567 & (1+
  v_int_90_2605)<=v_int_90_2604 | -1+res=v_int_90_2604 & nmin_58=nmin & 1+
  nmin_2545=nmin & v_int_90_2604<=v_int_90_2605 & nmin<=nmin_2567 | -1+
  res=v_int_90_2605 & nmin_58=nmin & 1+nmin_2567=nmin & 1<=nmin & (-1+
  nmin)<=nmin_2545 & (1+v_int_90_2605)<=v_int_90_2604 & (1+nmin_2545)<=h) & 
  (2+nmin_2567)<=h))) --> MHGT(res,nmin),
 (exists(nmin_58:MHGT(v_int_90_2608,nmin_2567) & 
  MHGT(v_int_90_2609,nmin_2545) & (exists(flted_26_2535:-1+
  res=v_int_90_2608 & nmin_58=nmin & 1+nmin_2567=nmin & 1<=nmin & (-1+
  nmin)<=nmin_2545 & v_int_90_2608<=v_int_90_2609 & 
  nmin_2545<=flted_26_2535) | exists(flted_26_2535:-1+res=v_int_90_2609 & 
  nmin_58=nmin & 1+nmin_2545=nmin & 1<=nmin & nmin<=nmin_2567 & 
  nmin_2567<=flted_26_2535 & (1+v_int_90_2609)<=v_int_90_2608) | 
  exists(flted_26_2535:-1+res=v_int_90_2608 & nmin_58=nmin & 1+
  nmin_2545=nmin & 1<=nmin & nmin<=nmin_2567 & nmin_2567<=flted_26_2535 & 
  v_int_90_2608<=v_int_90_2609) | exists(flted_26_2535:-1+
  res=v_int_90_2609 & nmin_58=nmin & 1+nmin_2567=nmin & 1<=nmin & (-1+
  nmin)<=nmin_2545 & (1+v_int_90_2609)<=v_int_90_2608 & 
  nmin_2545<=flted_26_2535)))) --> MHGT(res,nmin),
 (nmin=0 & res=0) --> MHGT(res,nmin)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:

Stop Omega... 2060 invocations 
30 false contexts at: ( (141,12)  (140,12)  (139,12)  (138,18)  (138,12)  (138,12)  (127,10)  (126,10)  (125,10)  (124,16)  (124,10)  (124,10)  (120,8)  (119,8)  (118,8)  (117,14)  (117,8)  (117,8)  (135,12)  (134,12)  (133,12)  (132,18)  (132,12)  (132,12)  (113,2)  (112,25)  (112,19)  (112,6)  (112,2)  (112,2) )

Total verification time: 2.2 second(s)
	Time spent in main process: 0.75 second(s)
	Time spent in child processes: 1.45 second(s)
