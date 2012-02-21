/usr/local/bin/mona

Processing file "ll-del2.ss"
Parsing ll-del2.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...
Starting Omega...oc

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  a <notin> S  | a <in> S 
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m,S1: res::ll2<m,S1>@M[Orig][LHSCase]&
                                m<=n & A(a,S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::ll2<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&(a <notin> S  | a <in> S ) & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 1::
                              res::ll2<m,S1>@M[Orig][LHSCase]&(S1=S & 
                              a <notin> S  | S1<subset> S  & a <in> S ) & 
                              m<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S1= & S= & S1=S) --> A(a,S,S1),
 (S1=S & S= & S1=) --> A(a,S,S1),
 (exists(S1_725:exists(v_723:exists(S1_593:exists(v_590:(S1_593= | 
  S1_593=union(S1_725,{v_723})) & S=union(S1_593,{v_590}) & S1_593=S1 & 
  a=v_590))))) --> A(a,S,S1),
 (exists(m_592:exists(n_642:exists(v_node_24_532':exists(v_node_24_735:exists(m_733:exists(m:exists(m_738:exists(m_780:exists(n:exists(v_bool_20_534':exists(v_bool_23_533':exists(x:exists(r_737:exists(res:exists(S1_781:exists(v_779:exists(S1_739:exists(v_736:exists(S1_593:exists(v_590:(S1_734= & 
  (1+m_592=n & S1_593=S_643 & 1+n_642=n & v_node_24_532'=res & v_590=v_736 & 
  v_node_24_735=r_737 & m_733=0 & S1_734=S1_739 & m=1 & m_738=0 & 
  !(v_bool_20_534') & (1+a)<=v_736 & !(v_bool_23_533') & r_737=null & 
  x!=null & res!=null & A(a,S_643,S1_734) & 1<=n | 1+m_592=n & 
  S1_593=S_643 & 1+n_642=n & v_node_24_532'=res & v_590=v_736 & 
  v_node_24_735=r_737 & m_733=0 & S1_734=S1_739 & m=1 & m_738=0 & 
  !(v_bool_20_534') & !(v_bool_23_533') & r_737=null & (1+v_736)<=a & 
  x!=null & res!=null & A(a,S_643,S1_734) & 1<=n) | (1+m_592=n & 
  S1_593=S_643 & 1+n_642=n & v_node_24_532'=res & v_590=v_736 & 
  v_node_24_735=r_737 & -1+m_733=m_780 & S1_734=S1_739 & -2+m=m_780 & -1+
  m_738=m_780 & (2+m_780)<=n & !(v_bool_20_534') & (1+a)<=v_736 & 
  !(v_bool_23_533') & x!=null & r_737!=null & res!=null & 
  A(a,S_643,S1_734) | 1+m_592=n & S1_593=S_643 & 1+n_642=n & 
  v_node_24_532'=res & v_590=v_736 & v_node_24_735=r_737 & -1+m_733=m_780 & 
  S1_734=S1_739 & -2+m=m_780 & -1+m_738=m_780 & (2+m_780)<=n & 
  !(v_bool_20_534') & !(v_bool_23_533') & (1+v_736)<=a & x!=null & 
  r_737!=null & res!=null & A(a,S_643,S1_734)) & S1_734=union(S1_781,
  {v_779})) & S1=union(S1_739,{v_736}) & S=union(S1_593,
  {v_590})))))))))))))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.85 second(s)
	Time spent in main process: 0.36 second(s)
	Time spent in child processes: 0.49 second(s)
