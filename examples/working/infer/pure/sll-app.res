
Processing file "sll-app.ss"
Parsing sll-app.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append_sll$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ xl<=ys]
!!! REL :  D(r,xs,t,yl,m,xn,yn)
!!! POST:  yl>=xs & yl>=r & t>=yl & xn>=1 & m>=xn & m=yn+xn
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [xl,ys,D]
              EBase exists (Expl)(Impl)[xn; xs; xl; yn; ys; 
                    yl](ex)x::sll<xn,xs,xl>@M[Orig][LHSCase] * 
                    y::sll<yn,ys,yl>@M[Orig][LHSCase]&1<=xn&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(r,t,m: x::sll<m,r,t>@M[Orig][LHSCase]&
                                D(r,xs,t,yl,m,xn,yn)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[xn; xs; xl; yn; ys; 
                  yl](ex)x::sll<xn,xs,xl>@M[Orig][LHSCase] * 
                  y::sll<yn,ys,yl>@M[Orig][LHSCase]&1<=xn&
                  {FLOW,(20,21)=__norm}
                    EBase true&xl<=ys & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(r_685,t_686,
                              m_687: x::sll<m_687,r_685,t_686>@M[Orig][LHSCase]&
                              yl>=xs & yl>=r_685 & t_686>=yl & xn>=1 & 
                              m_687>=xn & m_687=yn+xn & 0<=xn & xs<=xl & 
                              0<=yn & ys<=yl&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xn=1 & m=yn+1 & xs<=yl & r<=yl & yl<=t & 0<=yn) --> D(r,xs,t,yl,m,xn,yn),
 (m_658=m-1 & yl=yl_596 & xn=xn_591+1 & yn=yn_594 & xs<=r_656 & r<=r_656 & 
  r_656<=t_657 & t_657<=t & xs<=xs_592 & r<=xs_592 & 2<=m & 0<=yn_594 & 
  0<=xn_591 & 
  D(r_656,xs_592,t_657,yl_596,m_658,xn_591,yn_594)) --> D(r,xs,t,yl,m,xn,yn)]
!!! NEW ASSUME:[ RELASS [D]: ( D(r_656,xs_592,t_657,yl_596,m_658,xn_591,yn_594)) -->  xs_592<=r_656 | t_657<r_656 & r_656<xs_592 | r_656<=(xs_592-1) & 
r_656<=t_657 & m_658<=0]
!!! NEW RANK:[]
Procedure append_sll$node~node SUCCESS

Termination checking result:

Stop Omega... 156 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.07 second(s)
	Time spent in child processes: 0.16 second(s)
