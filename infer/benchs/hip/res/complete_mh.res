
Processing file "complete_mh.ss"
Parsing complete_mh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node2... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 9::
                                t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 9::
                              
                              true&(([null=t][0=res]))&{FLOW,(20,21)=__norm}
                              or t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                                 (([t!=null]))&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure maxim$int~int... 
Procedure maxim$int~int SUCCESS

Checking procedure height$node2... 
!!! REL :  HGT(res)
!!! POST:  res>=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [t,HGT]
              EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                                (([HGT(res)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                              (([0<=res]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ ((v_int_100_880=res-1 & v_int_100_879<res | v_int_100_879=res-1 & 
  v_int_100_880<=(res-2)) & HGT(v_int_100_880) & 
  HGT(v_int_100_879)) --> HGT(res),
 (res=0) --> HGT(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node2 SUCCESS

Checking procedure insert$node2~int... 
!!! REL :  INS(t')
!!! POST:  t'!=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::ref [t]
                                t'::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                                (([INS(t')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::ref [t]
                              t'::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                              (([t'!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (t'!=null) --> INS(t'),
 (t'!=null & INS(aux_54')) --> INS(t')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Checking procedure is_perfect$node2... 
!!! REL :  PEF(res)
!!! POST:  res>=0 & 1>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PEF]
              EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                                (([PEF(res)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                              (([0<=res & res<=1]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=1) --> PEF(res),
 (res=0) --> PEF(res),
 (v_int_186_585'=res & PEF(v_int_186_585') & PEF(1)) --> PEF(res),
 ((res=0 & 2<=v_int_185_1218 | res=0 & v_int_185_1218<=0) & 
  PEF(v_int_185_1218)) --> PEF(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_perfect$node2 SUCCESS

Checking procedure maxim1$int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&(())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                    EAssume 5::
                      
                      true&(([res=a & b<=res]))&{FLOW,(20,21)=__norm}
                      or true&(([res=b & (1+a)<=res]))&{FLOW,(20,21)=__norm}
                      )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure maxim1$int~int SUCCESS

Checking procedure minim$int~int... 
Procedure minim$int~int SUCCESS

Checking procedure min_height$node2... 
!!! REL :  MHGT(res)
!!! POST:  res>=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [t,MHGT]
              EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::
                                t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                                (([MHGT(res)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 19::
                              t::complete3@M[Orig][LHSCase]@ rem br[{265,264}]&
                              (([0<=res]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ ((v_int_115_1291=res-1 & res<=(v_int_115_1292+1) | v_int_115_1292=res-1 & 
  res<=v_int_115_1291) & MHGT(v_int_115_1292) & 
  MHGT(v_int_115_1291)) --> MHGT(res),
 (res=0) --> MHGT(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure min_height$node2 SUCCESS

Checking procedure minim1$int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&(())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                    EAssume 7::
                      
                      true&(([res=b & res<=a]))&{FLOW,(20,21)=__norm}
                      or true&(([res=a & (1+res)<=b]))&{FLOW,(20,21)=__norm}
                      )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure minim1$int~int SUCCESS

Termination checking result:

Stop Omega... 633 invocations 
0 false contexts at: ()

Total verification time: 0.35 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.18 second(s)
