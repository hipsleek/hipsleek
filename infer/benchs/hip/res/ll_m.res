
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                    y::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                  y::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::
                                x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::
                              
                              q_1012::node<Anon_1026,q_1027>@M[Orig][] * 
                              x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                              ([a=1][q_1012!=null][x!=null]))&
                              {FLOW,(20,21)=__norm}
                              or x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
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
!!! REL :  A(x')
!!! POST:  x'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&(([A(x')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              true&(([null=x']))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (x'=null) --> A(x')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              x::node<Anon_1229,q_1230>@M[Orig][]&(
                              ([x!=null][Anon_1229=res]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 27::
                              x::node<Anon_1242,q_1243>@M[Orig][]&(
                              ([q_1243=res][x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                res::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              x::node<Anon_1256,q_1257>@M[Orig][] * 
                              q_1257::node<Anon_1271,q_1272>@M[Orig][] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                              ([res=q_1272][q_1257!=null][x!=null]))&
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 71::
                                x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 71::
                              x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                x'::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              tmp_102'::node<Anon_1595,next_107_844'>@M[Orig][] * 
                              x'::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                              ([next_107_844'=null]
                               [x=res & x=tmp_102' & res!=null]))&
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
!!! REL :  REVERSE(xs')
!!! POST:  xs'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REVERSE]
              EBase xs::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                    ys::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::ref [xs;ys]
                                ys'::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (([REVERSE(xs')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase xs::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                  ys::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 52::ref [xs;ys]
                              ys'::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                              ([null=xs']))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (xs'=null) --> REVERSE(xs')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                    y::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                  y::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(flted_165_98,
                                Anon_15: x::node<Anon_15,flted_165_98>@M[Orig][]&
                                (([null=flted_165_98][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              x::node<Anon_15,flted_165_98>@M[Orig][]&(
                              ([flted_165_98=null][x!=null]))&
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                EXISTS(flted_153_100,
                                Anon_14: x::node<Anon_14,flted_153_100>@M[Orig][]&
                                (([null=flted_153_100][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              x::node<Anon_14,flted_153_100>@M[Orig][]&(
                              ([flted_153_100=null][x!=null]))&
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
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(([1<=a]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 58::ref [x]
                                x'::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                                res::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(([1<=a]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 58::ref [x]
                              x'::ll1@M[Orig][LHSCase]@ rem br[{400,399}] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{400,399}]&(
                              ([2<=a][x'=x & x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 722 invocations 
2 false contexts at: ( (158,13)  (158,4) )

Total verification time: 1.32 second(s)
	Time spent in main process: 1.17 second(s)
	Time spent in child processes: 0.15 second(s)
