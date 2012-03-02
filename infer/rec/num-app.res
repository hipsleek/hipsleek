
Processing file "num-app.ss"
Parsing num-app.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure appN$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=n, 1<=n]
!!! REL :  A(n,m,res)
!!! POST:  n>=1 & res=m+n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,m,A]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&A(n,m,res)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&1<=n & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 1::
                      true&n>=1 & res=m+n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=1 & m=res-1) --> A(n,m,res),
 (v_int_12_522=n-1 & v_int_12_526=res-1 & 2<=n & 
  A(v_int_12_522,m,v_int_12_526)) --> A(n,m,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appN$int~int SUCCESS

Termination checking result:

Stop Omega... 68 invocations 
0 false contexts at: ()

Total verification time: 0.09 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.05 second(s)
