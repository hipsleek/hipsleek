Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure del$int~int... 
!!! REL :  B(n,a,res)
!!! POST:  a>=1 & n>=(1+a) & n=res+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,B]
              EBase emp&1<=a & a<n&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                emp&B(n,a,res)&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase emp&1<=a & a<n&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              emp&a>=1 & n>=(1+a) & n=res+1&
                              {FLOW,(22,23)=__norm}[])
!!! NEW RELS:[ (a=1 & n=res+1 & 1<=res) --> B(n,a,res),
 (v_int_22_572=res-1 & v_int_22_569=a-1 & v_int_22_568=n-1 & 2<=a & a<n & 
  B(v_int_22_568,v_int_22_569,v_int_22_572)) --> B(n,a,res)]
!!! NEW ASSUME:[]
Procedure del$int~int SUCCESS

Termination checking result:

Stop Omega... 45 invocations 
0 false contexts at: ()

Total verification time: 0.26 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.05 second(s)

