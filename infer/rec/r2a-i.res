
Processing file "r2a-i.ss"
Parsing r2a-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure length$node... 
INF-POST-FLAG: false
REL :  R(res,n)
POST:  n>=0 & n=res
PRE :  0<=n
OLD SPECS:  EInfer [R]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           ECase case {
                  n=0 -> EBase true&MayLoop&{FLOW,(1,23)=__flow}
                                 EAssume 1::
                                   true&R(res,n)&{FLOW,(20,21)=__norm}
                  ;
                  n!=0 -> EBase true&MayLoop&{FLOW,(1,23)=__flow}
                                  EAssume 2::
                                    true&R(res,n)&{FLOW,(20,21)=__norm}
                  
                  }
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         ECase case {
                n=0 -> EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                               EAssume 1::
                                 true&R(res,n) & n=0 & 0<=n&
                                 {FLOW,(20,21)=__norm}
                ;
                n!=0 -> EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                                EAssume 2::
                                  true&R(res,n) & n!=0 & 0<=n&
                                  {FLOW,(20,21)=__norm}
                
                }
NEW RELS: [ (n=0 & res=0) --> R(res,n), (n_556=0 & n=1 & res=r_24'+1 & R(r_24',n_556)) --> R(res,n), (res=r_24'+1 & n_556=n-1 & 2<=n & R(r_24',n_556)) --> R(res,n)]

Procedure length$node SUCCESS

Termination checking result:

Stop Omega... 114 invocations 
9 false contexts at: ( (21,15)  (21,22)  (24,4)  (24,11)  (24,11)  (23,12)  (23,19)  (23,8)  (23,4) )

Total verification time: 0.22 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.06 second(s)
