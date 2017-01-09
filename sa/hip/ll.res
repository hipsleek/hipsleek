Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int... 
!!! es_infer_vars_hp_rel: [H]
!!! >>>>>> no relevant vars with mismatch <<<<<<
Context of Verification Failure: File "sa/hip/ll.ss",Line:90,Col:10
Last Proving Location: File "sa/hip/ll.ss",Line:96,Col:22

ERROR: at sa/hip/ll.ss_90_10 
Message: Expect a node
 
Procedure create_list$int FAIL-2

Exception Failure("Expect a node") Occurred!

Error(s) detected when checking procedure create_list$int

Checking procedure delete$node~int... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_655]
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_678]
!!! es_infer_vars_hp_rel: [H,G,HP_655,HP_663]
!!! es_infer_vars_hp_rel: [H,G,HP_678]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 88::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 88::ref [x]
                              
                              EXISTS(val_66_662,v_node_66_697,
                              G: x'::node<val_66_662,v_node_66_697>@M[Orig] * 
                              G(x,x')&x'=x & a=1&{FLOW,(22,23)=__norm})[]
                              or EXISTS(val_68_688,v_node_68_701,
                                 G: x'::node<val_68_688,v_node_68_701>@M[Orig] * 
                                 G(x,x')&x'=x & 2<=a | x'=x & a<=0&
                                 {FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&a=1&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_66_567',next_66_568'>@L[Orig] * 
  HP_655(next_66_568',a,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_655(v_node_66_569',a,x) * x::node<val_66_662,v_node_66_569'>@M[Orig]&
  a=1&
  {FLOW,(22,23)=__norm}[]) --> v_node_66_569'::node<val_66_570',next_66_571'>@L[Orig] * 
  HP_663(next_66_571',x,a,v_node_66_569')&true&{FLOW,(1,25)=__flow}[],
 (HP_663(v_node_66_697,x,a,v_node_66_674) * 
  v_node_66_674::node<val_66_673,v_node_66_697>@M[Orig] * 
  x::node<val_66_662,v_node_66_697>@M[Orig]&a=1&
  {FLOW,(22,23)=__norm}[]) --> G(x,x)&true&{FLOW,(22,23)=__norm}[],
 (H(x)&a!=1&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_68_575',next_68_576'>@L[Orig] * 
  HP_678(next_68_576',a,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_678(v_node_68_579',a,x) * x::node<val_68_688,v_node_68_579'>@M[Orig]&
  v_int_68_578'+(1*1)=a & a!=1&
  {FLOW,(22,23)=__norm}[]) --> H(v_node_68_579')&true&{FLOW,(22,23)=__norm}[],
 (x::node<val_68_688,v_node_68_701>@M[Orig]&true&
  {FLOW,(22,23)=__norm}[]) --> G(x,x)&true&{FLOW,(22,23)=__norm}[]]
Procedure delete$node~int SUCCESS

Checking procedure delete_val$node~int... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_711]
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_711]
!!! es_infer_vars_hp_rel: [H,G,HP_711]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 92::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 92::ref [x]
                              
                              EXISTS(G: htrue * G(x,x')&res=x' & x=x' & 
                              x'=null&{FLOW,(22,23)=__norm})[]
                              or EXISTS(a',next_81_719,
                                 G: x'::node<a',next_81_719>@M[Orig] * 
                                 G(x,x')&a=a' & next_81_719=res & x=x' & 
                                 x'!=null&{FLOW,(22,23)=__norm})[]
                              or EXISTS(v_int_81_733,HP_755,v_node_82_754,
                                 next_81_721,v_node_82_753,a',v_node_82_559',
                                 G: x'::node<v_int_81_733,next_81_721>@M[Orig] * 
                                 HP_755(v_node_82_754,next_81_721,v_node_82_753,a',res,x',x,a,v_node_82_559') * 
                                 G(x,x')&res=v_node_82_559' & a=a' & x=x' & 
                                 a'<v_int_81_733 & x'!=null | 
                                 res=v_node_82_559' & a=a' & x=x' & 
                                 v_int_81_733<a' & x'!=null&
                                 {FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&v_node_79_545'=x' & x'=x & x=null&{FLOW,(22,23)=__norm}[]) --> G(x,x)&
  true&{FLOW,(22,23)=__norm}[],
 (HP_711(next_81_719,a,x) * x::node<a,next_81_719>@M[Orig]&
  v_node_81_551'=next_81_719 & x!=null&{FLOW,(22,23)=__norm}[]) --> G(x,x)&
  true&{FLOW,(22,23)=__norm}[],
 (H(x)&x!=null&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_81_546',next_81_547'>@L[Orig] * 
  HP_711(next_81_547',a,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_711(next_81_721,a,x) * x::node<v_int_81_733,next_81_721>@M[Orig]&
  v_int_81_733!=a & x!=null&{FLOW,(22,23)=__norm}[]) --> H(next_81_721)&true&
  {FLOW,(22,23)=__norm}[],
 (x::node<v_int_81_733,next_81_721>@M[Orig] * 
  v_node_82_559'::node<v_int_81_733,v_node_82_754>@M[Orig] * 
  HP_755(v_node_82_754,next_81_721,v_node_82_753,a,v_node_82_559',x,x,a,v_node_82_559')&
  v_int_81_733!=a & x!=null&{FLOW,(22,23)=__norm}[]) --> G(x,x)&true&
  {FLOW,(22,23)=__norm}[]]
Procedure delete_val$node~int SUCCESS

Checking procedure get_next_next$node... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_758]
!!! es_infer_vars_hp_rel: [H,G,HP_758,HP_766]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 84::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 84::ref [x]
                              EXISTS(val_43_765,v_node_43_773,val_43_772,
                              v_node_43_604',
                              G: x'::node<val_43_765,v_node_43_773>@M[Orig] * 
                              v_node_43_773::node<val_43_772,v_node_43_604'>@M[Orig] * 
                              G(x,x')&x'=x & res=v_node_43_604'&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&true&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_43_599',next_43_600'>@L[Orig] * 
  HP_758(next_43_600',x)&true&{FLOW,(1,25)=__flow}[],
 (HP_758(v_node_43_601',x) * x::node<val_43_765,v_node_43_601'>@M[Orig]&true&
  {FLOW,(22,23)=__norm}[]) --> v_node_43_601'::node<val_43_602',next_43_603'>@L[Orig] * 
  HP_766(next_43_603',x,v_node_43_601')&true&{FLOW,(1,25)=__flow}[],
 (x::node<val_43_765,v_node_43_773>@M[Orig] * 
  HP_766(v_node_43_604',x,v_node_43_773) * 
  v_node_43_773::node<val_43_772,v_node_43_604'>@M[Orig]&true&
  {FLOW,(22,23)=__norm}[]) --> G(x,x)&true&{FLOW,(22,23)=__norm}[]]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_776]
!!! es_infer_vars_hp_rel: [H,G,HP_776]
!!! es_infer_vars_hp_rel: [H,G,HP_776]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 85::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 85::ref [x]
                              
                              EXISTS(a',v_null_53_801,val_52_782,
                              v_node_53_817,
                              G: v_node_53_817::node<a',v_null_53_801>@M[Orig] * 
                              x'::node<val_52_782,v_node_53_817>@M[Orig] * 
                              G(x,x')&x'=x & a'=a & v_null_53_801=null&
                              {FLOW,(22,23)=__norm})[]
                              or EXISTS(val_52_784,v_node_52_807,
                                 G: x'::node<val_52_784,v_node_52_807>@M[Orig] * 
                                 G(x,x')&x'=x & v_node_52_807!=null&
                                 {FLOW,(22,23)=__norm})[]
                              )
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (HP_776(v_node_52_800,a,x) * x::node<val_52_782,v_node_53_817>@M[Orig]&
  v_node_52_800=null&{FLOW,(22,23)=__norm}[]) --> G(x,x)&true&
  {FLOW,(22,23)=__norm}[],
 (H(x)&true&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_52_585',next_52_586'>@L[Orig] * 
  HP_776(next_52_586',a,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_776(v_node_52_807,a,x) * x::node<val_52_784,v_node_52_807>@M[Orig]&
  v_node_52_807!=null&{FLOW,(22,23)=__norm}[]) --> H(v_node_52_807)&true&
  {FLOW,(22,23)=__norm}[],
 (x::node<val_52_784,v_node_52_807>@M[Orig]&v_node_52_807!=null&
  {FLOW,(22,23)=__norm}[]) --> G(x,x)&true&{FLOW,(22,23)=__norm}[]]
Procedure insert$node~int SUCCESS

Checking procedure set_next$node~node... 
!!! es_infer_vars_hp_rel: [H1,H2,G3]
!!! es_infer_vars_hp_rel: [H1,H2,G3,HP_822]
!!! OLD SPECS: ((None,[]),EInfer [H1,H2,G3]
              EBase H1(x) * H2(y)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 80::ref [x;y]
                                G3(x,x',y)&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H1(x) * H2(y)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 80::ref [x;y]
                              EXISTS(val_24_827,
                              G3: x'::node<val_24_827,y'>@M[Orig] * 
                              G3(x,x',y)&x'=x & y'=y&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H1(x) * H2(y)&true&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_24_615',next_24_616'>@M[Orig] * 
  HP_822(next_24_616',y,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_822(next_24_826,y,x) * x::node<val_24_827,y>@M[Orig]&true&
  {FLOW,(22,23)=__norm}[]) --> G3(x,x,y)&true&{FLOW,(22,23)=__norm}[]]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! es_infer_vars_hp_rel: [H,G]
!!! es_infer_vars_hp_rel: [H,G,HP_831]
!!! OLD SPECS: ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 82::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 82::ref [x]
                              EXISTS(val_34_836,
                              G: x'::node<val_34_836,next_34_610'>@M[Orig] * 
                              G(x,x')&x'=x & next_34_610'=null&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW HP RELS:[]
!!! NEW HP ASSUME:[ (H(x)&v_null_34_608'=null&
  {FLOW,(22,23)=__norm}[]) --> x::node<val_34_609',next_34_610'>@M[Orig] * 
  HP_831(next_34_610',v_null_34_608',null,x)&true&{FLOW,(1,25)=__flow}[],
 (HP_831(next_34_835,next_34_610',null,x) * 
  x::node<val_34_836,next_34_610'>@M[Orig]&next_34_610'=null&
  {FLOW,(22,23)=__norm}[]) --> G(x,x)&true&{FLOW,(22,23)=__norm}[]]
Procedure set_null$node SUCCESS

Termination checking result:

Stop Omega... 139 invocations 
0 false contexts at: ()

Total verification time: 0.69 second(s)
	Time spent in main process: 0.66 second(s)
	Time spent in child processes: 0.03 second(s)
