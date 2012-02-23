
Processing file "dll_ms.ss"
Parsing dll_ms.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node2~node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[q; 
                    p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{138,137}] * 
                    y::dll<p>@M[Orig][LHSCase]@ rem br[{138,137}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(q_27: x::dll<q_27>@M[Orig][LHSCase]@ rem br[{138,137}]&
                                (([q=q_27]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; 
                  p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{138,137}] * 
                  y::dll<p>@M[Orig][LHSCase]@ rem br[{138,137}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              x::dll<q_27>@M[Orig][LHSCase]@ rem br[{138,137}]&
                              (([q_27=q][x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Checking procedure insert$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{138,137}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(p_29: x::dll<p_29>@M[Orig][LHSCase]@ rem br[{138,137}]&
                                (([p=p_29]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{138,137}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::dll<p_29>@M[Orig][LHSCase]@ rem br[{138,137}]&
                              (([p_29=p][x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 201 invocations 
0 false contexts at: ()

Total verification time: 0.38 second(s)
	Time spent in main process: 0.34 second(s)
	Time spent in child processes: 0.04 second(s)
