
Processing file "num-del.ss"
Parsing num-del.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ 2<=n, 1<=n]
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
 ((res=v_int_14_544+1 & a=v_int_14_540+1 & n=v_int_14_539+1 & 
  0<=v_int_14_539 & 1<=v_int_14_540 | res=v_int_14_544+1 & a=v_int_14_540+
  1 & n=v_int_14_539+1 & v_int_14_540<=(0-1) & 0<=v_int_14_539) & 
  B(v_int_14_539,v_int_14_540,v_int_14_544)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 87 invocations 
0 false contexts at: ()

Total verification time: 0.09 second(s)
	Time spent in main process: 0.04 second(s)
	Time spent in child processes: 0.05 second(s)
