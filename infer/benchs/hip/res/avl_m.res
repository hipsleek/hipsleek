
Processing file "avl_m.ss"
Parsing avl_m.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure build_avl1$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    y::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 46::
                                res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  y::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 46::
                              res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([x!=null][res!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl1$node~node SUCCESS

Checking procedure build_avl2$node~node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ y!=null | x=null]
!!! OLD SPECS: ((None,[]),EInfer [x,y]
              EBase exists (Expl)(Impl)[Anon_12; Anon_13; Anon_14; 
                    Anon_15](ex)y::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    z::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                    ([x!=null]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_12; Anon_13; Anon_14; 
                  Anon_15](ex)y::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  z::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                  ([x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][y!=null | x=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 50::
                              x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([x!=null][y!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl2$node~node~node SUCCESS

Checking procedure get_max$int~int... 
Procedure get_max$int~int SUCCESS

Checking procedure height$node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(([null=x][0=res]))&{FLOW,(20,21)=__norm}
                              or x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                 (([0<=res][x!=null]))&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node SUCCESS

Checking procedure insert$node~int... 
( [(480::,0 ); (480::,0 ); (434::,0 ); (434::,0 ); (433::,1 ); (433::,1 )]) :avl_m.ss:188: 26: bind: node  v_node_188_965'::node<val_188_966',height_188_967',left_188_968',right_188_969'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):avl_m.ss:188: 26:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(480::,0 ); (480::,0 ); (434::,0 ); (434::,0 ); (433::,1 ); (433::,1
          )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_188_965'=v_node_184_1595 & v_node_188_965'=null |-  v_node_188_965'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

( [(440::,0 ); (440::,0 ); (434::,1 ); (434::,1 ); (433::,1 ); (433::,1 )]) :avl_m.ss:209: 16: bind: node  v_node_209_1114'::node<val_209_1115',height_209_1116',left_209_1117',right_209_1118'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):avl_m.ss:209: 16:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(440::,0 ); (440::,0 ); (434::,1 ); (434::,1 ); (433::,1 ); (433::,1
          )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_209_1114'=v_node_206_1721 & v_node_209_1114'=null |-  v_node_209_1114'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

Procedure insert$node~int result FAIL-1

Checking procedure insert_inline$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 73::
                                res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 73::
                              
                              res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([res!=null][null=x]))&{FLOW,(20,21)=__norm}
                              or res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                 (([x!=null][res!=null]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert_inline$node~int SUCCESS

Checking procedure merge$node~node... 
Procedure merge$node~node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d]
              EBase a::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    b::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    c::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    d::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase a::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  b::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  c::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  d::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 21::
                              res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([res!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_left$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_double_right$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d]
              EBase a::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    b::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    c::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    d::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase a::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  b::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  c::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  d::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([res!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_right$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_left$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase l::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    rl::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    rr::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase l::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  rl::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  rr::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([res!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_left$node~node~node SUCCESS

Checking procedure rotate_right$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [ll,lr,r,res]
              EBase ll::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    lr::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                    r::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase ll::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  lr::avl1@M[Orig][LHSCase]@ rem br[{654,653}] * 
                  r::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              res::avl1@M[Orig][LHSCase]@ rem br[{654,653}]&(
                              ([res!=null]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_right$node~node~node SUCCESS

Termination checking result:

Stop Omega... 3055 invocations 
18 false contexts at: ( (467,17)  (467,24)  (471,3)  (471,22)  (471,10)  (470,15)  (470,27)  (470,8)  (469,14)  (469,25)  (469,8)  (469,3)  (352,12)  (348,20)  (292,14)  (288,20)  (222,14)  (201,12) )

Total verification time: 5.28 second(s)
	Time spent in main process: 4.58 second(s)
	Time spent in child processes: 0.7 second(s)
