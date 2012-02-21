
Processing file "sll-app.ss"
Parsing sll-app.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append_sll$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ xl<=ys]
!!! REL :  D(r,xs,t,yl,m,xn,yn)
!!! POST:  yl>=r & yl>=xs & t>=yl & yn>=0 & m>=(1+yn) & m=xn+yn
!!! PRE :  xs<=yl & 1<=xn & 0<=yn
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
                    EBase true&xl<=ys & xs<=yl & 1<=xn & 0<=yn & MayLoop&
                          {FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::sll<m,r,t>@M[Orig][LHSCase]&yl>=r & 
                              yl>=xs & t>=yl & yn>=0 & m>=(1+yn) & m=xn+yn & 
                              0<=xn & xs<=xl & 0<=yn & ys<=yl&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(qmin_620:1+yn=m & 1<=m & yl<=t & xn=1 & 
  exists(qs_574:exists(ql_575:exists(xl:exists(ys:ys<=yl & r<=qmin_620 & 
  xs<=qmin_620 & qmin_620<=qs_574 & qs_574<=ql_575 & ql_575<=xl & 
  xl<=ys)))))) --> D(r,xs,t,yl,m,xn,yn),
 (exists(xl_593:exists(xl:1<=m_658 & r_656<=t_657 & 1+xn_591=xn & 
  yn_594=yn & yl_596=yl & -1+m=m_658 & t_657<=t & 1<=xn & 0<=yn & 
  D(r_656,xs_592,t_657,yl_596,m_658,xn_591,yn_594) & 
  exists(qmin_659:exists(ys_595:xl_593<=xl & ys_595<=yl & qmin_659<=r_656 & 
  xs<=qmin_659 & r<=qmin_659 & xs_592<=xl_593 & 
  qmin_659<=xs_592))))) --> D(r,xs,t,yl,m,xn,yn)]
!!! NEW ASSUME:[ RELASS [D]: ( D(r_656,xs_592,t_657,yl_596,m_658,xn_591,yn_594)) -->  xs_592<=r_656 | t_657<r_656 & r_656<xs_592 | r_656<=(xs_592-1) & 
r_656<=t_657 & m_658<=0]
!!! NEW RANK:[]
Procedure append_sll$node~node SUCCESS

Termination checking result:

Stop Omega... 208 invocations 
0 false contexts at: ()

Total verification time: 0.56 second(s)
	Time spent in main process: 0.36 second(s)
	Time spent in child processes: 0.2 second(s)
