Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n, 1<=n]
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & res>=a & res+1=n
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 69::
                                true&B(n,a,res)&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase true&2<=n & MayLoop&{FLOW,(1,23)=__flow}[]
                    EAssume 69::
                      true&a>=1 & res>=a & res+1=n&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[ (a=1 & res=n-1 & 2<=n) --> B(n,a,res),
 ((res=v_int_27_560+1 & v_int_27_556=a-1 & v_int_27_555=n-1 & 1<=n & 2<=a | 
  res=v_int_27_560+1 & v_int_27_556=a-1 & v_int_27_555=n-1 & a<=0 & 1<=n) & 
  B(v_int_27_555,v_int_27_556,v_int_27_560)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 92 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.06 second(s)
