Translating global variables to procedure parameters...

Checking procedure delete1$node~int... 
Mona is running ... 
Starting Omega...oc

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{206,205}]&
                    (())&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(S1: res::ll<S1>@M[Orig][LHSCase]@ rem br[{206,205}]&
                                (([A(a,S,S1)]))&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{206,205}]&
                  (())&{FLOW,(22,23)=__norm}[]
                    EBase emp&(([MayLoop]))&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(S1: res::ll<S1>@M[Orig][LHSCase]@ rem br[{206,205}]&
                              (
                              ([S1=S & a <notin> S  | S1<subset> S  & 
                                 a <in> S ]
                               ))&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (S1= & S=) --> A(a,S,S1),
 (exists(v_613:exists(S1_615:v_613=a & S1=S1_615 & S=union(S1_615,{v_613}) & 
  S!=()))) --> A(a,S,S1),
 (exists(v_613:exists(S1_615:exists(v_653:exists(S1_655:exists(res:exists(x:exists(v_bool_27_573':exists(v_bool_24_574':exists(v_node_28_572':exists(v_node_28_652:exists(q_654:S_636=S1_615 & 
  S1_655=S1_651 & (q_654=v_node_28_652 & v_613=v_653 & v_node_28_572'=res & 
  !(v_bool_24_574') & (1+a)<=v_653 & !(v_bool_27_573') & x!=null & 
  res!=null & A(a,S_636,S1_651) | q_654=v_node_28_652 & v_613=v_653 & 
  v_node_28_572'=res & !(v_bool_24_574') & (1+v_653)<=a & 
  !(v_bool_27_573') & x!=null & res!=null & A(a,S_636,S1_651)) & 
  S1=union(S1_655,{v_653}) & S=union(S1_615,{v_613}) & 
  S!=())))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete1$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.47 second(s)
	Time spent in main process: 0.29 second(s)
	Time spent in child processes: 0.18 second(s)
