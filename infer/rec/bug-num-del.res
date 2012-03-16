
Processing file "bug-num-del.ss"
Parsing bug-num-del.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n, 1<=n]
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & n>=(1+a) & n=res+1
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase true&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&B(n,a,res)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&2<=n & MayLoop&{FLOW,(1,23)=__flow}
                    EAssume 1::
                      true&a>=1 & n>=(1+a) & n=res+1&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (a=1 & n=res+1 & 1<=res) --> B(n,a,res),
 ((res=v_int_27_547+1 & a=v_int_27_543+1 & n=v_int_27_542+1 & 
  0<=v_int_27_542 & 1<=v_int_27_543 | res=v_int_27_547+1 & a=v_int_27_543+
  1 & n=v_int_27_542+1 & v_int_27_543<=(0-1) & 0<=v_int_27_542) & 
  B(v_int_27_542,v_int_27_543,v_int_27_547)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 99 invocations 
0 false contexts at: ()

Total verification time: 0.1 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.06 second(s)
