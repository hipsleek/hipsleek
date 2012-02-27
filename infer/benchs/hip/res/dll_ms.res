
Processing file "dll_ms.ss"
Parsing dll_ms.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[q; 
                    p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                    y::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(q_164: x::dll<q_164>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([q=q_164]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; 
                  p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                  y::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(q_1444: x::dll<q_1444>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][q=q_1444]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
( [(364::,0 ); (364::,0 )]) :dll_ms.ss:242: 10: bind: node  v_node_242_973'::node<val_242_974',prev_242_975',next_242_976'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):dll_ms.ss:242: 10:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(364::,0 ); (364::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_242_973'=q_1599 & v_node_242_973'=null |-  v_node_242_973'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

Procedure Call:dll_ms.ss:253: 2: 
Verification Context:(Line:235,Col:9)
Proving precondition in method delete$node~int for spec:
 ((None,[]),EBase exists (Expl)(Impl)[p_1672](ex)v_node_253_1008'::dll<p_1672>@M[Orig][LHSCase]@ rem br[{528}]&
                  (([null!=v_node_253_1008']))&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              EXISTS(p_1293: v_node_253_1008'::dll<p_1293>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([p_1293=p_1672]))&{FLOW,(20,21)=__norm}))
Current States: [ x'::node<Anon_1661,p_1659,q_1662>@M[Orig][] * q_1662::dll<self_1660>@M[Orig]@ rem br[{529,528}]&(([
                                                                    tmp_161'=null]
                                                                    [!(v_bool_240_1009')]
                                                                    [x=x' & 
                                                                    x=self_1660 & 
                                                                    x'!=null]
                                                                    [p_1659=p]
                                                                    [v_node_253_1008'=q_1662]
                                                                    [a'=a & 
                                                                    a'!=1 & 
                                                                    1+
                                                                    v_int_253_1007'=a']
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure delete$node~int result FAIL-1

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
!!! REL :  A(x')
!!! POST:  x'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&(([A(x')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]@ rem br[{529,528}]&
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
              EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]@ rem br[{529,528}]&
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
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]@ rem br[{529,528}]&
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
              EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              EXISTS(Anon_2063,p_2064,q_2065,
                              self_2066: self_2066::node<Anon_2063,p_2064,q_2065>@M[Orig][] * 
                              q_2065::dll<self_2066>@M[Orig]@ rem br[{529,528}]&
                              (
                              ([x=self_2066 & self_2066!=null]
                               [Anon_19=p_2064][res=Anon_2063]))&
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
              EBase exists (Expl)(Impl)[Anon_32](ex)x::dll<Anon_32>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_32](ex)x::dll<Anon_32>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(q_2102,self_2103,f_2104,Anon_2105,
                              next_169_2106: q_2102::dll<self_2103>@M[Orig]@ rem br[{529,528}] * 
                              self_2103::node<Anon_2105,prev_169_1109',next_169_2106>@M[Orig][]&
                              (
                              ([x=self_2103 & self_2103!=null]
                               [null=next_169_2106][null=prev_169_1109']
                               [res=q_2102]))&
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
              EBase exists (Expl)(Impl)[Anon_42](ex)x::dll<Anon_42>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(Anon_43: res::dll<Anon_43>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_42](ex)x::dll<Anon_42>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              
                              EXISTS(p_2173,Anon_2174,p_2175,q_2176,
                              Anon_2177: p_2173::node<Anon_2174,p_2175,q_2176>@M[Orig][] * 
                              res::dll<Anon_2177>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (
                              ([Anon_2177=q_2176 & q_2176!=null]
                               [x=p_2173 & x!=null][Anon_42=p_2175]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(self_2178,Anon_2179,p_2180,
                                 q_2181: self_2178::node<Anon_2179,p_2180,q_2181>@M[Orig][]&
                                 (
                                 ([x=self_2178 & self_2178!=null][null=res]
                                  [null=q_2181][Anon_42=p_2180]))&
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
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(p_162: x::dll<p_162>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_162]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(p_2275: x::dll<p_2275>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][p=p_2275]))&{FLOW,(20,21)=__norm}))
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
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 99::
                                EXISTS(p_138: x::dll<p_138>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_138]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 99::
                              EXISTS(p_2869: x::dll<p_2869>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][p=p_2869]))&{FLOW,(20,21)=__norm}))
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
              EBase exists (Expl)(Impl)[Anon_28](ex)x::dll<Anon_28>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(Anon_29: x'::dll<Anon_29>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_28](ex)x::dll<Anon_28>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              
                              EXISTS(tmp_3235,f_3236,Anon_3237,
                              p_3238: tmp_3235::node<Anon_3237,p_3238,next_120_1157'>@M[Orig][]&
                              (
                              ([res=x & res=tmp_3235 & res!=null][null=x']
                               [null=next_120_1157'][Anon_28=p_3238]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(tmp_3239,f_3240,Anon_3241,p_3242,
                                 Anon_3243: tmp_3239::node<Anon_3241,p_3242,next_127_1173'>@M[Orig][] * 
                                 x'::dll<Anon_3243>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                 (
                                 ([res=x & res=tmp_3239 & res!=null]
                                  [x'!=null][null=next_127_1173']
                                  [Anon_28=p_3242][Anon_3243=null]))&
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
                    q](ex)xs::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                    ys::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::ref [xs;ys]
                                EXISTS(Anon_47: ys'::dll<Anon_47>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([REVERSE(xs')]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  q](ex)xs::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                  ys::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::ref [xs;ys]
                              EXISTS(Anon_3491: ys'::dll<Anon_3491>@M[Orig][LHSCase]@ rem br[{529,528}]&
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
                    Anon_34](ex)x::dll<Anon_33>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                    y::dll<Anon_34>@M[Orig][LHSCase]@ rem br[{529,528}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(Anon_35: x::dll<Anon_35>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_33; 
                  Anon_34](ex)x::dll<Anon_33>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                  y::dll<Anon_34>@M[Orig][LHSCase]@ rem br[{529,528}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              
                              EXISTS(Anon_3619: x::dll<Anon_3619>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][null=y][Anon_3619=Anon_33]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(Anon_3620: x::dll<Anon_3620>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                 (([y!=null][x!=null][Anon_3620=Anon_33]))&
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
              EBase exists (Expl)(Impl)[Anon_39](ex)x::dll<Anon_39>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(Anon_40,Anon_41,
                                r: x::node<Anon_40,Anon_41,r>@M[Orig][]&(
                                ([x!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39](ex)x::dll<Anon_39>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(Anon_3643,Anon_3644,
                              r_3645: x::node<Anon_3643,Anon_3644,r_3645>@M[Orig][]&
                              (([x!=null][null=r_3645][Anon_39=Anon_3644]))&
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
              EBase exists (Expl)(Impl)[Anon_36](ex)x::dll<Anon_36>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::
                                EXISTS(Anon_37,Anon_38,
                                r: x::node<Anon_37,Anon_38,r>@M[Orig][]&(
                                ([x!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36](ex)x::dll<Anon_36>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 43::
                              EXISTS(Anon_3679,Anon_3680,
                              r_3681: x::node<Anon_3679,Anon_3680,r_3681>@M[Orig][]&
                              (([x!=null][null=r_3681][Anon_3680=Anon_36]))&
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

Checking procedure split1$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (([1<=a]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::ref [x]
                                EXISTS(p_145,
                                Anon_48: x'::dll<p_145>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                                res::dll<Anon_48>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_145]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (([1<=a]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 84::ref [x]
                              
                              EXISTS(p_4056,
                              Anon_4057: x'::dll<p_4056>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                              res::dll<Anon_4057>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (
                              ([x'=x & Anon_4057=x' & x'!=null][p=p_4056]
                               [1=a]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(p_4058,
                                 Anon_4059: x'::dll<p_4058>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                                 res::dll<Anon_4059>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                 (([2<=a][x'=x & x'!=null][p=p_4058]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1146 invocations 
7 false contexts at: ( (488,6)  (196,13)  (196,4)  (44,4)  (44,11)  (46,4)  (46,11) )

Total verification time: 2.33 second(s)
	Time spent in main process: 2.15 second(s)
	Time spent in child processes: 0.18 second(s)
