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
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::
                                emp&A(n,m,res)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 67::
                      emp&n>=1 & res=m+n&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (n=1 & m=res-1) --> A(n,m,res),
 (m'=m & v_int_12_558=res-1 & n=v_int_12_554+1 & 1<=v_int_12_554 & 
  A(v_int_12_554,m',v_int_12_558)) --> A(n,m,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appN$int~int SUCCESS

Termination checking result:

Stop Omega... 61 invocations 
0 false contexts at: ()

Total verification time: 0.24 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.04 second(s)
