
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                    y::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 24::
                                x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                  y::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 24::
                              x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              
                              q_1016::node<Anon_1030,q_1031>@M[Orig][] * 
                              x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                              ([a=1][q_1016!=null][x!=null]))&
                              {FLOW,(20,21)=__norm}
                              or x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&(([A(x')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              true&(([null=x']))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (x'=null) --> A(x')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
!!! REL :  EMPT1(res)
!!! POST:  res
!!! PRE :  true
!!! REL :  EMPT2(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [EMPT1,EMPT2]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      ECase case {
                             x=null -> ((None,[]),EBase true&MayLoop&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 4::
                                                            true&(
                                                            ([EMPT1(res)]))&
                                                            {FLOW,(20,21)=__norm})
                             ;
                             x!=null -> ((None,[]),EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 5::
                                                             true&(
                                                             ([EMPT2(res)]))&
                                                             {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    ECase case {
                           x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 4::
                                                          true&(
                                                          ([res][null=x]))&
                                                          {FLOW,(20,21)=__norm})
                           ;
                           x!=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 5::
                                                           true&(
                                                           ([!(res)][
                                                            x!=null]))&
                                                           {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (1<=res) --> EMPT1(res),
 (res<=0) --> EMPT2(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              x::node<Anon_1237,q_1238>@M[Orig][]&(
                              ([x!=null][Anon_1237=res]))&
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              x::node<Anon_1250,q_1251>@M[Orig][]&(
                              ([q_1251=res][x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                res::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              x::node<Anon_1264,q_1265>@M[Orig][] * 
                              q_1265::node<Anon_1279,q_1280>@M[Orig][] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                              ([res=q_1280][q_1265!=null][x!=null]))&
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::
                                x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::ref [x]
                                x'::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 21::ref [x]
                              tmp_102'::node<Anon_1603,next_113_846'>@M[Orig][] * 
                              x'::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                              ([next_113_846'=null]
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
              EBase xs::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                    ys::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::ref [xs;ys]
                                ys'::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&
                                (([REVERSE(xs')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase xs::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                  ys::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 53::ref [xs;ys]
                              ys'::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                    y::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                  y::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_171_98,
                                Anon_15: x::node<Anon_15,flted_171_98>@M[Orig][]&
                                (([null=flted_171_98][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              x::node<Anon_15,flted_171_98>@M[Orig][]&(
                              ([flted_171_98=null][x!=null]))&
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                EXISTS(flted_159_100,
                                Anon_14: x::node<Anon_14,flted_159_100>@M[Orig][]&
                                (([null=flted_159_100][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              x::node<Anon_14,flted_159_100>@M[Orig][]&(
                              ([flted_159_100=null][x!=null]))&
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
              EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(([1<=a]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::ref [x]
                                x'::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                                res::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(([1<=a]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 59::ref [x]
                              x'::ll1@M[Orig][LHSCase]@ rem br[{401,400}] * 
                              res::ll1@M[Orig][LHSCase]@ rem br[{401,400}]&(
                              ([2<=a][x'=x & x!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 741 invocations 
6 false contexts at: ( (164,13)  (164,4)  (42,17)  (42,24)  (43,7)  (43,14) )

Total verification time: 1.39 second(s)
	Time spent in main process: 1.19 second(s)
	Time spent in child processes: 0.2 second(s)
