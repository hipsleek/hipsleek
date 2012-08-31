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
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 66::ref [x]
                                EXISTS(b_32,
                                s1: x'::bst<s1,b_32>@M[Orig][LHSCase]&
                                A(s,res,s1) & b_32=b&{FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[s; b](ex)x::bst<s,b>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}[]
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 66::ref [x]
                              EXISTS(b_32,
                              s1: x'::bst<s1,b_32>@M[Orig][LHSCase]&b_32=b & 
                              res>=s & s1>=res&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (s<=res & res<=s1) --> A(s,res,s1),
 (s_615=s & tmp_35'=res & s1_629=s1 & 
  A(s_615,tmp_35',s1_629)) --> A(s,res,s1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Termination checking result:

Stop Omega... 82 invocations 
0 false contexts at: ()

Total verification time: 0.29 second(s)
	Time spent in main process: 0.25 second(s)
	Time spent in child processes: 0.04 second(s)
