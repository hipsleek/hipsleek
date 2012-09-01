Translating global variables to procedure parameters...

Checking procedure delete2$node~int... 
Mona is running ... 
Starting Omega...oc

!!! REL :  A(a,S,S1)
!!! POST:  S1=S & a <notin> S  | S1<subset> S  & a <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{196,195}]&(
                    ())&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 64::
                                EXISTS(m,
                                S1: res::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{196,195}]&
                                (([m<=n][A(a,S,S1)]))&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::ll2<n,S>@M[Orig][LHSCase]@ rem br[{196,195}]&(
                  ())&{FLOW,(20,21)=__norm}[]
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}[]
                            EAssume 64::
                              EXISTS(m,
                              S1: res::ll2<m,S1>@M[Orig][LHSCase]@ rem br[{196,195}]&
                              (
                              ([m<=n]
                               [S1=S & a <notin> S  | S1<subset> S  & 
                                 a <in> S ]
                               ))&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (S1= & S=) --> A(a,S,S1),
 (exists(v_589:exists(S1_592:exists(m_591:exists(v_bool_23_546':exists(x':exists(v_bool_20_547':exists(m:exists(v_node_23_537':exists(res:exists(r_590:exists(n:exists(a':(a'=v_589 & 
  a=v_589 & -1+n=m_591 & r_590=v_node_23_537' & res=v_node_23_537' & 
  m=m_591 & v_bool_20_547'<=0 & m_591<=-2 & x'!=null & 1<=v_bool_23_546' | 
  a'=v_589 & a=v_589 & -1+n=m_591 & r_590=v_node_23_537' & 
  res=v_node_23_537' & m=m_591 & v_bool_20_547'<=0 & x'!=null & 
  1<=v_bool_23_546' & 0<=m_591) & S1=S1_592 & S=union(S1_592,{v_589}) & 
  S!=()))))))))))))) --> A(a,S,S1),
 (exists(v_589:exists(S1_592:exists(v_644:exists(S1_647:exists(m_591:exists(res:exists(x:exists(v_bool_20_547':exists(v_bool_23_546':exists(m:exists(v_node_24_545':exists(n_616:exists(m_641:exists(n:exists(m_646:exists(v_node_24_643:exists(r_645:S_617=S1_592 & 
  S1_647=S1_642 & (r_645=v_node_24_643 & 1+m_646=m & -1+n=m_591 & 1+
  m_641=m & n_616=m_591 & v_589=v_644 & v_node_24_545'=res & 0<=m & (-1+
  m)<=m_591 & (1+a)<=v_644 & !(v_bool_23_546') & !(v_bool_20_547') & 
  x!=null & res!=null & A(a,S_617,S1_642) & 0<=m_591 | r_645=v_node_24_643 & 
  1+m_646=m & -1+n=m_591 & 1+m_641=m & n_616=m_591 & v_589=v_644 & 
  v_node_24_545'=res & 0<=m & (-1+m)<=m_591 & (1+v_644)<=a & 
  !(v_bool_23_546') & !(v_bool_20_547') & x!=null & res!=null & 
  A(a,S_617,S1_642) & 0<=m_591) & S1=union(S1_647,{v_644}) & S!=() & 
  S=union(S1_592,{v_589}))))))))))))))))))) --> A(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Termination checking result:


0 false contexts at: ()

Total verification time: 0.48 second(s)
	Time spent in main process: 0.3 second(s)
	Time spent in child processes: 0.18 second(s)
