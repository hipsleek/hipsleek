
Processing file "dll_ms.ss"
Parsing dll_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[q; 
                    p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{485,484}] * 
                    y::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(q_141: x::dll<q_141>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (([q=q_141]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; 
                  p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{485,484}] * 
                  y::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(q_1348: x::dll<q_1348>@M[Orig][LHSCase]@ rem br[{485,484}]&
                              (([x!=null][q=q_1348]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
!!! REL :  A(x')
!!! POST:  x'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&(([A(x')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
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
              EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
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
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
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
              EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              EXISTS(Anon_1860,p_1861,q_1862,
                              self_1863: self_1863::node<Anon_1860,p_1861,q_1862>@M[Orig][] * 
                              q_1862::dll<self_1863>@M[Orig]@ rem br[{485,484}]&
                              (
                              ([x=self_1863 & self_1863!=null]
                               [Anon_19=p_1861][res=Anon_1860]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_32](ex)x::dll<Anon_32>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_32](ex)x::dll<Anon_32>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(q_1899,self_1900,f_1901,Anon_1902,
                              next_169_1903: q_1899::dll<self_1900>@M[Orig]@ rem br[{485,484}] * 
                              self_1900::node<Anon_1902,prev_169_1016',next_169_1903>@M[Orig][]&
                              (
                              ([x=self_1900 & self_1900!=null]
                               [null=next_169_1903][null=prev_169_1016']
                               [res=q_1899]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_42](ex)x::dll<Anon_42>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(Anon_43: res::dll<Anon_43>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_42](ex)x::dll<Anon_42>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              
                              EXISTS(p_1970,Anon_1971,p_1972,q_1973,
                              Anon_1974: p_1970::node<Anon_1971,p_1972,q_1973>@M[Orig][] * 
                              res::dll<Anon_1974>@M[Orig][LHSCase]@ rem br[{485,484}]&
                              (
                              ([Anon_1974=q_1973 & q_1973!=null]
                               [x=p_1970 & x!=null][Anon_42=p_1972]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(self_1975,Anon_1976,p_1977,
                                 q_1978: self_1975::node<Anon_1976,p_1977,q_1978>@M[Orig][]&
                                 (
                                 ([x=self_1975 & self_1975!=null][null=res]
                                  [null=q_1978][Anon_42=p_1977]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(p_139: x::dll<p_139>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (([p=p_139]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(p_2072: x::dll<p_2072>@M[Orig][LHSCase]@ rem br[{485,484}]&
                              (([x!=null][p=p_2072]))&{FLOW,(20,21)=__norm}))
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
!!! Inferred Pure :[ x!=null, x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::
                                EXISTS(p_127: x::dll<p_127>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (([p=p_127]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 84::
                              EXISTS(p_2666: x::dll<p_2666>@M[Orig][LHSCase]@ rem br[{485,484}]&
                              (([x!=null][p=p_2666]))&{FLOW,(20,21)=__norm}))
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
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_28](ex)x::dll<Anon_28>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(Anon_29: x'::dll<Anon_29>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_28](ex)x::dll<Anon_28>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              
                              EXISTS(tmp_3032,f_3033,Anon_3034,
                              p_3035: tmp_3032::node<Anon_3034,p_3035,next_120_1064'>@M[Orig][]&
                              (
                              ([res=x & res=tmp_3032 & res!=null][null=x']
                               [null=next_120_1064'][Anon_28=p_3035]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(tmp_3036,f_3037,Anon_3038,p_3039,
                                 Anon_3040: tmp_3036::node<Anon_3038,p_3039,next_127_1080'>@M[Orig][] * 
                                 x'::dll<Anon_3040>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                 (
                                 ([res=x & res=tmp_3036 & res!=null]
                                  [x'!=null][null=next_127_1080']
                                  [Anon_28=p_3039][Anon_3040=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
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
              EBase exists (Expl)(Impl)[p; 
                    q](ex)xs::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}] * 
                    ys::dll<q>@M[Orig][LHSCase]@ rem br[{485,484}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 68::ref [xs;ys]
                                EXISTS(Anon_47: ys'::dll<Anon_47>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (([REVERSE(xs')]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  q](ex)xs::dll<p>@M[Orig][LHSCase]@ rem br[{485,484}] * 
                  ys::dll<q>@M[Orig][LHSCase]@ rem br[{485,484}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 68::ref [xs;ys]
                              EXISTS(Anon_3288: ys'::dll<Anon_3288>@M[Orig][LHSCase]@ rem br[{485,484}]&
                              (([null=xs']))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs'=null) --> REVERSE(xs')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_33; 
                    Anon_34](ex)x::dll<Anon_33>@M[Orig][LHSCase]@ rem br[{485,484}] * 
                    y::dll<Anon_34>@M[Orig][LHSCase]@ rem br[{485,484}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(Anon_35: x::dll<Anon_35>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_33; 
                  Anon_34](ex)x::dll<Anon_33>@M[Orig][LHSCase]@ rem br[{485,484}] * 
                  y::dll<Anon_34>@M[Orig][LHSCase]@ rem br[{485,484}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              
                              EXISTS(Anon_3416: x::dll<Anon_3416>@M[Orig][LHSCase]@ rem br[{485,484}]&
                              (([x!=null][null=y][Anon_3416=Anon_33]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(Anon_3417: x::dll<Anon_3417>@M[Orig][LHSCase]@ rem br[{485,484}]&
                                 (([y!=null][x!=null][Anon_3417=Anon_33]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_39](ex)x::dll<Anon_39>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(Anon_40,Anon_41,
                                r: x::node<Anon_40,Anon_41,r>@M[Orig][]&(
                                ([x!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39](ex)x::dll<Anon_39>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(Anon_3440,Anon_3441,
                              r_3442: x::node<Anon_3440,Anon_3441,r_3442>@M[Orig][]&
                              (([x!=null][null=r_3442][Anon_39=Anon_3441]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_36](ex)x::dll<Anon_36>@M[Orig][LHSCase]@ rem br[{485,484}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::
                                EXISTS(Anon_37,Anon_38,
                                r: x::node<Anon_37,Anon_38,r>@M[Orig][]&(
                                ([x!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36](ex)x::dll<Anon_36>@M[Orig][LHSCase]@ rem br[{485,484}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 43::
                              EXISTS(Anon_3476,Anon_3477,
                              r_3478: x::node<Anon_3476,Anon_3477,r_3478>@M[Orig][]&
                              (([x!=null][null=r_3478][Anon_3477=Anon_36]))&
                              {FLOW,(20,21)=__norm}))
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

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1058 invocations 
7 false contexts at: ( (492,10)  (196,13)  (196,4)  (44,4)  (44,11)  (46,4)  (46,11) )

Total verification time: 0.53 second(s)
	Time spent in main process: 0.37 second(s)
	Time spent in child processes: 0.16 second(s)
