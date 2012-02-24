
Processing file "bst-remove-min.ss"
Parsing bst-remove-min.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure remove_min$node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(s,res,s1)
!!! POST:  res>=s & s1>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[s; 
                    b](ex)x::bst<s,b>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [x]
                                EXISTS(b_30,
                                s1: x'::bst<s1,b_30>@M[Orig][LHSCase]&
                                A(s,res,s1) & b_30=b&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[s; b](ex)x::bst<s,b>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::ref [x]
                              x'::bst<s1,b_30>@M[Orig][LHSCase]&b_30=b & 
                              res>=s & s1>=res & s<=b&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res<=s1 & exists(pl_578:s<=pl_578 & pl_578<=res) & 
  exists(b:s1<=b)) --> A(s,res,s1),
 (A(s_600,tmp_33',s1_628) & s1=s1_628 & 
  exists(qs_579:exists(b_30:exists(lg_577:s_600=s & 
  exists(v_580:qs_579<=b_30 & lg_577=b_30 & exists(b_601:v_580<=qs_579 & 
  s<=b_601 & s1_628<=b_601 & b_601<=v_580))))) & tmp_33'=res) --> A(s,res,s1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Termination checking result:

Stop Omega... 117 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.06 second(s)
