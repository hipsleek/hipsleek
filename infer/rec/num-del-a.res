Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & n>=(1+a) & n=res+1
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase true&1<=a & a<n&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 70::
                                true&B(n,a,res)&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase true&1<=a & a<n&{FLOW,(20,21)=__norm}[]
                    EBase true&2<=n & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 70::
                              true&a>=1 & n>=(1+a) & n=res+1&
                              {FLOW,(20,21)=__norm}[])
!!! NEW RELS:[ (a=1 & n=res+1 & 1<=res) --> B(n,a,res),
 (v_int_22_559=res-1 & a=v_int_22_555+1 & n=v_int_22_554+1 & 
  1<=v_int_22_555 & v_int_22_555<v_int_22_554 & 
  B(v_int_22_554,v_int_22_555,v_int_22_559)) --> B(n,a,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.25 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.05 second(s)
