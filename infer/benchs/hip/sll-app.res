
Processing file "sll-app.ss"
Parsing sll-app.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure append_sll$node~node... 
Inferred Heap:[]
Inferred Pure:[ xn!=0, xn!=0, xl<=ys]

INF-POST-FLAG: true
REL :  D(r,xs,t,yl,m,xn,yn)
POST:  yl>=r & yl>=xs & t>=yl & yn>=0 & xn>=1 & xn+yn=m
PRE :  xs<=yl & 1<=xn & 0<=yn
OLD SPECS:  EInfer [xl,ys,xn,D]
   EBase exists (Expl)(Impl)[xn; xs; xl; yn; ys; 
         yl](ex)x::sll<xn,xs,xl>@M[Orig][LHSCase] * 
         y::sll<yn,ys,yl>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(r,t,m: x::sll<m,r,t>@M[Orig][LHSCase]&
                     D(r,xs,t,yl,m,xn,yn)&{FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[xn; xs; xl; yn; ys; 
       yl](ex)x::sll<xn,xs,xl>@M[Orig][LHSCase] * 
       y::sll<yn,ys,yl>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
         EBase true&xl<=ys & xs<=yl & 1<=xn & 0<=yn & MayLoop&
               {FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::sll<m,r,t>@M[Orig][LHSCase]&yl>=r & yl>=xs & t>=yl & 
                   yn>=0 & xn>=1 & xn+yn=m & 0<=xn & xs<=xl & 0<=yn & ys<=yl&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (xn=1 & yn=m-1 & xs<=yl & r<=yl & yl<=t & 1<=m) --> D(r,xs,t,yl,m,xn,yn), (yl_595=yl & m=m_657+1 & yn_593=yn & xn_590=xn-1 & r<=xs_591 & xs<=xs_591 & 
  xs_591<=r_655 & r_655<=t_656 & t_656<=t & 1<=m_657 & 0<=yn & 1<=xn & 
  D(r_655,xs_591,t_656,yl_595,m_657,xn_590,yn_593)) --> D(r,xs,t,yl,m,xn,yn)]

Procedure append_sll$node~node SUCCESS

Termination checking result:

Stop Omega... 269 invocations 
0 false contexts at: ()

Total verification time: 0.63 second(s)
	Time spent in main process: 0.34 second(s)
	Time spent in child processes: 0.29 second(s)
