Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n]
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & n>=(1+a) & n=res+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                emp&B(n,a,res)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&2<=n & MayLoop&{FLOW,(1,25)=__flow}[]
                    EAssume 70::
                      emp&a>=1 & n>=(1+a) & n=res+1&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (a=1 & n=res+1 & 1<=res) --> B(n,a,res),
 (((res=v_int_14_570+1 & n=v_int_14_566+1 & a=v_int_14_567+1 & 
  v_int_14_567<=(0-1) & 0<=v_int_14_566) | (res=v_int_14_570+1 & 
  n=v_int_14_566+1 & a=v_int_14_567+1 & 0<=v_int_14_566 & 
  1<=v_int_14_567)) & 
  B(v_int_14_566,v_int_14_567,v_int_14_570)) --> B(n,a,res)]
!!! NEW ASSUME:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 68 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.05 second(s)

