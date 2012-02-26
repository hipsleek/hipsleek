
Processing file "num-del-a.ss"
Parsing num-del-a.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & res>=a & res+1=n
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase true&1<=a & a<n&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                true&B(n,a,res)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&1<=a & a<n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              true&a>=1 & res>=a & res+1=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (a=1 & 1+res=n & 2<=n) --> B(n,a,res),
 ((1+v_int_22_542)<=v_int_22_541 & 1<=v_int_22_542 & -1+n=v_int_22_541 & -1+
  a=v_int_22_542 & -1+res=v_int_22_546 & 
  B(v_int_22_541,v_int_22_542,v_int_22_546)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 57 invocations 
0 false contexts at: ()

Total verification time: 0.21 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.05 second(s)
