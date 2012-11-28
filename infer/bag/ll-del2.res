Translating global variables to procedure parameters...

Checking procedure delete2$node~int... 
Mona is running ... 
Starting Omega...oc

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{204,203}]&(
                    ())&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::
                                EXISTS(m,
                                S1: res::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{204,203}]&
                                (([m<=n][A(a,S,S1)]))&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{204,203}]&(
                  ())&{FLOW,(22,23)=__norm}[]
                    EBase emp&(([MayLoop]))&{FLOW,(1,25)=__flow}[]
                            EAssume 64::
                              EXISTS(m,
                              S1: res::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{204,203}]&
                              (
                              ([m<=n]
                               [S1=S & a <notin> S  | S1<subset> S  & 
                                 a <in> S ]
                               ))&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (S1= & S=) --> A(a,S,S1),
 (exists(v_609:exists(S1_612:exists(m_611:exists(v_bool_23_566':exists(x':exists(v_bool_20_567':exists(m:exists(v_node_23_557':exists(res:exists(r_610:exists(n:exists(a':(a'=v_609 & 
  a=v_609 & -1+n=m_611 & r_610=v_node_23_557' & res=v_node_23_557' & 
  m=m_611 & v_bool_20_567'<=0 & m_611<=-2 & x'!=null & 1<=v_bool_23_566' | 
  a'=v_609 & a=v_609 & -1+n=m_611 & r_610=v_node_23_557' & 
  res=v_node_23_557' & m=m_611 & v_bool_20_567'<=0 & x'!=null & 
  1<=v_bool_23_566' & 0<=m_611) & S1=S1_612 & S=union(S1_612,{v_609}) & 
  S!=()))))))))))))) --> A(a,S,S1),
 (exists(v_609:exists(S1_612:exists(v_664:exists(S1_667:exists(m_611:exists(res:exists(x:exists(v_bool_20_567':exists(v_bool_23_566':exists(m:exists(v_node_24_565':exists(n_636:exists(m_661:exists(n:exists(m_666:exists(v_node_24_663:exists(r_665:S_637=S1_612 & 
  S1_667=S1_662 & (r_665=v_node_24_663 & 1+m_666=m & -1+n=m_611 & 1+
  m_661=m & n_636=m_611 & v_609=v_664 & v_node_24_565'=res & 0<=m & (-1+
  m)<=m_611 & (1+a)<=v_664 & !(v_bool_23_566') & !(v_bool_20_567') & 
  x!=null & res!=null & A(a,S_637,S1_662) & 0<=m_611 | r_665=v_node_24_663 & 
  1+m_666=m & -1+n=m_611 & 1+m_661=m & n_636=m_611 & v_609=v_664 & 
  v_node_24_565'=res & 0<=m & (-1+m)<=m_611 & (1+v_664)<=a & 
  !(v_bool_23_566') & !(v_bool_20_567') & x!=null & res!=null & 
  A(a,S_637,S1_662) & 0<=m_611) & S1=union(S1_667,{v_664}) & S!=() & 
  S=union(S1_612,{v_609}))))))))))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.52 second(s)
	Time spent in main process: 0.32 second(s)
	Time spent in child processes: 0.2 second(s)
