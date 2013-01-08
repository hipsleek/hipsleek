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
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::ref [x]
                                EXISTS(b_28,
                                s1: x'::bst<s1,b_28>@M[Orig][LHSCase]&
                                A(s,res,s1) & b_28=b&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[s; b](ex)x::bst<s,b>@M[Orig][LHSCase]&
                  true&{FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 66::ref [x]
                              EXISTS(b_28,
                              s1: x'::bst<s1,b_28>@M[Orig][LHSCase]&b_28=b & 
                              res>=s & s1>=res&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (s<=res & res<=s1) --> A(s,res,s1),
 (v_int_39_571'=res & s_633=s & s1_647=s1 & 
  A(s_633,v_int_39_571',s1_647)) --> A(s,res,s1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Termination checking result:

Stop Omega... 75 invocations 
0 false contexts at: ()

Total verification time: 0.32 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.04 second(s)
