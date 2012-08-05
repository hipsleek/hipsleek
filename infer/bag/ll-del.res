/usr/local/bin/mona

Processing file "ll-del.ss"
Parsing ll-del.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure delete1$node~int... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(S1: res::ll<S1>@M[Orig][LHSCase]&
                                A(a,S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S](ex)x::ll<S>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(S1_679: res::ll<S1_679>@M[Orig][LHSCase]&
                              (S1_679=S & a <notin> S  | S1_679<subset> S  & 
                              a <in> S )&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S= & S1=S) --> A(a,S,S1),
 (S1=S & S= & S1=) --> A(a,S,S1),
 (exists(S1_642:exists(v_641:exists(S1_585:exists(v_583:(S1_585= | 
  S1_585=union(S1_642,{v_641})) & S=union(S1_585,{v_583}) & S1_585=S1 & 
  a=v_583))))) --> A(a,S,S1),
 (exists(v_node_28_539':exists(v_node_28_646:exists(v_bool_24_541':exists(v_bool_27_540':exists(x:exists(q_648:exists(res:exists(S1_662:exists(v_661:exists(S1_649:exists(v_647:exists(S1_585:exists(v_583:(S1_645= & 
  (S1_585=S_606 & v_node_28_539'=res & v_583=v_647 & v_node_28_646=q_648 & 
  S1_645=S1_649 & !(v_bool_24_541') & (1+a)<=v_647 & !(v_bool_27_540') & 
  q_648=null & x!=null & res!=null & A(a,S_606,S1_645) | S1_585=S_606 & 
  v_node_28_539'=res & v_583=v_647 & v_node_28_646=q_648 & S1_645=S1_649 & 
  !(v_bool_24_541') & !(v_bool_27_540') & q_648=null & (1+v_647)<=a & 
  x!=null & res!=null & A(a,S_606,S1_645)) | (S1_585=S_606 & 
  v_node_28_539'=res & v_583=v_647 & v_node_28_646=q_648 & S1_645=S1_649 & 
  !(v_bool_24_541') & (1+a)<=v_647 & !(v_bool_27_540') & x!=null & 
  q_648!=null & res!=null & A(a,S_606,S1_645) | S1_585=S_606 & 
  v_node_28_539'=res & v_583=v_647 & v_node_28_646=q_648 & S1_645=S1_649 & 
  !(v_bool_24_541') & !(v_bool_27_540') & (1+v_647)<=a & x!=null & 
  q_648!=null & res!=null & A(a,S_606,S1_645)) & S1_645=union(S1_662,
  {v_661})) & S1=union(S1_649,{v_647}) & S=union(S1_585,
  {v_583}))))))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete1$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.2 second(s)
