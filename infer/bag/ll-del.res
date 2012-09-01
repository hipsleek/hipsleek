Translating global variables to procedure parameters...

Checking procedure delete1$node~int... 
Mona is running ... 
Starting Omega...oc

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{198,197}]&
                    (())&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                EXISTS(S1: res::ll<S1>@M[Orig][LHSCase]@ rem br[{198,197}]&
                                (([A(a,S,S1)]))&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]@ rem br[{198,197}]&
                  (())&{FLOW,(20,21)=__norm}[]
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              EXISTS(S1: res::ll<S1>@M[Orig][LHSCase]@ rem br[{198,197}]&
                              (
                              ([S1=S & a <notin> S  | S1<subset> S  & 
                                 a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (S1= & S=) --> A(a,S,S1),
 (exists(v_593:exists(S1_595:v_593=a & S1=S1_595 & S=union(S1_595,{v_593}) & 
  S!=()))) --> A(a,S,S1),
 (exists(v_593:exists(S1_595:exists(v_633:exists(S1_635:exists(res:exists(x:exists(v_bool_27_553':exists(v_bool_24_554':exists(v_node_28_552':exists(v_node_28_632:exists(q_634:S_616=S1_595 & 
  S1_635=S1_631 & (q_634=v_node_28_632 & v_593=v_633 & v_node_28_552'=res & 
  !(v_bool_24_554') & (1+a)<=v_633 & !(v_bool_27_553') & x!=null & 
  res!=null & A(a,S_616,S1_631) | q_634=v_node_28_632 & v_593=v_633 & 
  v_node_28_552'=res & !(v_bool_24_554') & (1+v_633)<=a & 
  !(v_bool_27_553') & x!=null & res!=null & A(a,S_616,S1_631)) & 
  S1=union(S1_635,{v_633}) & S=union(S1_595,{v_593}) & 
  S!=())))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete1$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.46 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.18 second(s)
