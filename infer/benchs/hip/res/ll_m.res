
Processing file "ll_m.ss"
Parsing ll_m.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    y::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  y::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              
                              q_1029::node<Anon_1043,q_1044>@M[Orig][] * 
                              x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([a=1][q_1029!=null][x!=null]))&
                              {FLOW,(20,21)=__norm}
                              or x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                 ([x!=null & 2<=a | a<=0 & x!=null]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::
                                EXISTS(flted_141_103,
                                Anon_14: x::node<Anon_14,flted_141_103>@M[Orig][] * 
                                res::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([null=flted_141_103][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 27::
                              x::node<Anon_14,flted_141_103>@M[Orig][] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([flted_141_103=null][x!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                res::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              x::node<Anon_1266,q_1267>@M[Orig][] * 
                              q_1267::node<Anon_1281,q_1282>@M[Orig][] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([res=q_1282][q_1267!=null][x!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::
                                x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                x'::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              tmp_105'::node<Anon_1605,next_111_855'>@M[Orig][] * 
                              x'::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([next_111_855'=null]
                               [x=res & x=tmp_105' & res!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    y::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  y::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_173_99,
                                Anon_16: x::node<Anon_16,flted_173_99>@M[Orig][]&
                                (([null=flted_173_99][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              x::node<Anon_16,flted_173_99>@M[Orig][]&(
                              ([flted_173_99=null][x!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                EXISTS(flted_160_101,
                                Anon_15: x::node<Anon_15,flted_160_101>@M[Orig][]&
                                (([null=flted_160_101][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              x::node<Anon_15,flted_160_101>@M[Orig][]&(
                              ([flted_160_101=null][x!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x,res]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(([1<=a]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::ref [x]
                                x'::ll1@M[Orig][LHSCase]@ rem br[{403,402}] * 
                                res::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(([1<=a]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 59::ref [x]
                              x'::ll1@M[Orig][LHSCase]@ rem br[{403,402}] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{403,402}]&(
                              ([2<=a][x'=x & x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 699 invocations 
2 false contexts at: ( (165,13)  (165,4) )

Total verification time: 1.4 second(s)
	Time spent in main process: 1.27 second(s)
	Time spent in child processes: 0.13 second(s)
