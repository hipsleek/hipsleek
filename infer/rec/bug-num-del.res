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
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                emp&B(n,a,res)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&2<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 69::
                      emp&a>=1 & res>=a & res+1=n&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (a=1 & res=n-1 & 2<=n) --> B(n,a,res),
 ((res=v_int_27_579+1 & v_int_27_575=a-1 & v_int_27_574=n-1 & 1<=n & 2<=a | 
  res=v_int_27_579+1 & v_int_27_575=a-1 & v_int_27_574=n-1 & a<=0 & 1<=n) & 
  B(v_int_27_574,v_int_27_575,v_int_27_579)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 88 invocations 
0 false contexts at: ()

Total verification time: 0.27 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.06 second(s)
