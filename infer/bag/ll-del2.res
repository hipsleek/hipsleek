/usr/local/bin/mona

Processing file "ll-del2.ss"
Parsing ll-del2.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure delete2$node~int... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
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
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(m_796,
                              S1_797: res::ll2<m_796,S1_797>@M[Orig][LHSCase]&
                              m_796<=n & (S1_797=S & a <notin> S  | 
                              S1_797<subset> S  & a <in> S )&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S= & S1=S) --> A(a,S,S1),
 (S1=S & S= & S1=) --> A(a,S,S1),
 (exists(S1_708:exists(v_706:exists(S1_593:exists(v_590:(S1_593= | 
  S1_593=union(S1_708,{v_706})) & S=union(S1_593,{v_590}) & S1_593=S1 & 
  a=v_590))))) --> A(a,S,S1),
 (exists(m_592:exists(n_630:exists(v_node_24_532':exists(v_node_24_718:exists(m_716:exists(m:exists(m_721:exists(m_753:exists(n:exists(v_bool_20_534':exists(v_bool_23_533':exists(x:exists(r_720:exists(res:exists(S1_754:exists(v_752:exists(S1_722:exists(v_719:exists(S1_593:exists(v_590:(S1_717= & 
  (1+m_592=n & S1_593=S_631 & 1+n_630=n & v_node_24_532'=res & v_590=v_719 & 
  v_node_24_718=r_720 & m_716=0 & S1_717=S1_722 & m=1 & m_721=0 & 
  !(v_bool_20_534') & (1+a)<=v_719 & !(v_bool_23_533') & r_720=null & 
  x!=null & res!=null & A(a,S_631,S1_717) & 1<=n | 1+m_592=n & 
  S1_593=S_631 & 1+n_630=n & v_node_24_532'=res & v_590=v_719 & 
  v_node_24_718=r_720 & m_716=0 & S1_717=S1_722 & m=1 & m_721=0 & 
  !(v_bool_20_534') & !(v_bool_23_533') & r_720=null & (1+v_719)<=a & 
  x!=null & res!=null & A(a,S_631,S1_717) & 1<=n) | (1+m_592=n & 
  S1_593=S_631 & 1+n_630=n & v_node_24_532'=res & v_590=v_719 & 
  v_node_24_718=r_720 & -1+m_716=m_753 & S1_717=S1_722 & -2+m=m_753 & -1+
  m_721=m_753 & (2+m_753)<=n & !(v_bool_20_534') & (1+a)<=v_719 & 
  !(v_bool_23_533') & x!=null & r_720!=null & res!=null & 
  A(a,S_631,S1_717) | 1+m_592=n & S1_593=S_631 & 1+n_630=n & 
  v_node_24_532'=res & v_590=v_719 & v_node_24_718=r_720 & -1+m_716=m_753 & 
  S1_717=S1_722 & -2+m=m_753 & -1+m_721=m_753 & (2+m_753)<=n & 
  !(v_bool_20_534') & !(v_bool_23_533') & (1+v_719)<=a & x!=null & 
  r_720!=null & res!=null & A(a,S_631,S1_717)) & S1_717=union(S1_754,
  {v_752})) & S1=union(S1_722,{v_719}) & S=union(S1_593,
  {v_590})))))))))))))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.47 second(s)
	Time spent in main process: 0.07 second(s)
	Time spent in child processes: 0.4 second(s)
