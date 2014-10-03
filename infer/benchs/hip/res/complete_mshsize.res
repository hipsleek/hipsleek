
Processing file "complete_mshsize.ss"
Parsing complete_mshsize.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node2... 
!!! REL :  CNT(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CNT]
              EBase exists (Expl)(Impl)[n; h; 
                    nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([0<=n][nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(n_69,h_70,
                                nmin_71: t::complete<n_69,h_70,nmin_71>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([n=n_69 & 0<=n_69 & CNT(res,n)]
                                 [h_70=h & nmin=nmin_71 & nmin_71<=h_70 & 
                                   0<=nmin_71]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; 
                  nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=n][0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(n_1156,h_1157,
                              nmin_1158: t::complete<n_1156,h_1157,nmin_1158>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([n=res & n=n_1156 & 0<=n]
                               [nmin=nmin_1158 & h=h_1157 & nmin<=h & 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & n=0) --> CNT(res,n),
 (n=0 & res=0) --> CNT(res,n),
 (CNT(cleft_72',n_974) & CNT(cright_73',n_1001) & n=1+n_1001+n_974 & 1+
  cleft_72'+cright_73'=res & 1<=n_974 & 0<=n_1001) --> CNT(res,n),
 (CNT(cright_73',n_1001) & CNT(cleft_72',n_974) & n=1+n_1001+n_974 & 1+
  cleft_72'+cright_73'=res & 0<=n_974 & 0<=n_1001) --> CNT(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure maxim$int~int... 
Procedure maxim$int~int SUCCESS

Checking procedure height$node2... 
!!! REL :  HGT(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [HGT]
              EBase exists (Expl)(Impl)[n; h; 
                    nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([0<=n][nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(h_67,nmin_68,
                                m: t::complete<m,h_67,nmin_68>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([0<=m & HGT(m,n)]
                                 [nmin_68=nmin & h=h_67 & h=res & 
                                   nmin_68<=h_67 & 0<=nmin_68]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; 
                  nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=n][0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(h_1456,nmin_1457,
                              m_1458: t::complete<m_1458,h_1456,nmin_1457>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([n=m_1458 & 0<=n]
                               [nmin=nmin_1457 & res=h & res=h_1456 & 
                                 nmin<=h & 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> HGT(m,n),
 (HGT(m_1281,n_1253) & HGT(m_1316,n_1288) & n=1+n_1253+n_1288 & 1<=n_1253 & 
  0<=n_1288 & m<=(m+m_1316) & 1+m_1281+m_1316=m & (2+m_1316)<=m) --> HGT(m,n),
 (HGT(m_1284,n_1253) & HGT(m_1318,n_1288) & n=1+n_1253+n_1288 & 0<=n_1288 & 
  0<=n_1253 & m<=(m+m_1318) & 1+m_1284+m_1318=m & (1+m_1318)<=m) --> HGT(m,n),
 (n=0 & m=0) --> HGT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node2 SUCCESS

Checking procedure insert$node2~int... 
Procedure insert$node2~int SUCCESS

Checking procedure is_perfect$node2... 
!!! REL :  PEF(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PEF]
              EBase exists (Expl)(Impl)[n; h; 
                    nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([0<=n][nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(h_51,nmin_52,
                                m: t::complete<m,h_51,nmin_52>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([0<=m & PEF(m,n)]
                                 [h=h_51 & nmin=nmin_52 & (nmin!=h | 
                                   res=1) & (nmin=h | res=0) & 
                                   nmin_52<=h_51 & 0<=nmin_52]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; 
                  nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=n][0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              EXISTS(h_2878,nmin_2879,
                              m_2880: t::complete<m_2880,h_2878,nmin_2879>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([n=m_2880 & 0<=n]
                               [nmin=nmin_2879 & h=h_2878 & (nmin!=h | 
                                 res=1) & (nmin=h | res=0) & nmin<=h & 
                                 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> PEF(m,n),
 (n=0 & m=0) --> PEF(m,n),
 (exists(ml1_2720:1<=ml1_2720 & m+ml1_2720=ml1_2720+n & (1+
  ml1_2720)<=n)) --> PEF(m,n),
 (PEF(m_2764,n_2685) & PEF(m_2675,n_2654) & 0<=n_2654 & 1+n_2654+n_2685=n & 
  (1+n_2654)<=n & m<=(m+m_2764) & 1+m_2675+m_2764=m & (1+
  m_2764)<=m) --> PEF(m,n),
 (PEF(m_2677,n_2654) & m<=(m+m_2677) & (1+m_2677)<=m & m+n_2654=m_2677+n & 
  m<=(m_2677+n)) --> PEF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_perfect$node2 SUCCESS

Checking procedure minim$int~int... 
Procedure minim$int~int SUCCESS

Checking procedure min_height$node2... 
!!! REL :  MHGT(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MHGT]
              EBase exists (Expl)(Impl)[n; h; 
                    nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                    (([0<=n][nmin<=h & 0<=nmin]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(h_62,nmin_63,
                                m: t::complete<m,h_62,nmin_63>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                                (
                                ([0<=m & MHGT(m,n)]
                                 [h_62=h & nmin=nmin_63 & nmin=res & 
                                   nmin_63<=h_62 & 0<=nmin_63]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h; 
                  nmin](ex)t::complete<n,h,nmin>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                  (([0<=n][0<=nmin & nmin<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(h_3178,nmin_3179,
                              m_3180: t::complete<m_3180,h_3178,nmin_3179>@M[Orig][LHSCase]@ rem br[{255,254,253}]&
                              (
                              ([n=m_3180 & 0<=n]
                               [res=nmin & res=nmin_3179 & h=h_3178 & 
                                 nmin<=h & 0<=nmin]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> MHGT(m,n),
 (MHGT(m_3003,n_2975) & MHGT(m_3038,n_3010) & n=1+n_2975+n_3010 & 
  1<=n_2975 & 0<=n_3010 & m<=(m+m_3038) & 1+m_3003+m_3038=m & (2+
  m_3038)<=m) --> MHGT(m,n),
 (MHGT(m_3006,n_2975) & MHGT(m_3040,n_3010) & n=1+n_2975+n_3010 & 
  0<=n_3010 & 0<=n_2975 & m<=(m+m_3040) & 1+m_3006+m_3040=m & (1+
  m_3040)<=m) --> MHGT(m,n),
 (n=0 & m=0) --> MHGT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Termination checking result:

Stop Omega... 2758 invocations 
30 false contexts at: ( (144,12)  (143,12)  (142,12)  (141,18)  (141,12)  (141,12)  (130,10)  (129,10)  (128,10)  (127,16)  (127,10)  (127,10)  (123,8)  (122,8)  (121,8)  (120,14)  (120,8)  (120,8)  (138,12)  (137,12)  (136,12)  (135,18)  (135,12)  (135,12)  (116,2)  (115,25)  (115,19)  (115,6)  (115,2)  (115,2) )

Total verification time: 2.74 second(s)
	Time spent in main process: 1.01 second(s)
	Time spent in child processes: 1.73 second(s)
