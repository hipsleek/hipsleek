Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n, 1<=n]
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & res>=a & n=res+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                emp&B(n,a,res)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&2<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 69::
                      emp&a>=1 & res>=a & n=res+1&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (a=1 & res=n-1 & 2<=n) --> B(n,a,res),
 (((res=v_int_27_573+1 & n=v_int_27_569+1 & a=v_int_27_570+1 & 
  v_int_27_570<=(0-1) & 0<=v_int_27_569) | (res=v_int_27_573+1 & 
  n=v_int_27_569+1 & a=v_int_27_570+1 & 0<=v_int_27_569 & 
  1<=v_int_27_570)) & 
  B(v_int_27_569,v_int_27_570,v_int_27_573)) --> B(n,a,res)]
!!! NEW ASSUME:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 78 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.05 second(s)

