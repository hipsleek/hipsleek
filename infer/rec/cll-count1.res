Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node~node... 
dprint: cll-count1.ss:32: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(131::,0 ); (131::,0 )])]

Successful States:
[
 Label: [(131::,0 ); (131::,0 )]
 State:x::cll<p,n>@M[Orig][LHSCase]&x'=x & h'=h & h=p & x'=h' & v_bool_31_570' & x'=h' & v_bool_31_570'&{FLOW,(22,23)=__norm}[]
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop

 ]

dprint: cll-count1.ss:40: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(131::,1 ); (131::,1 )])]

Successful States:
[
 Label: [(131::,1 ); (131::,1 )]
 State:EXISTS(n_625: x'::node<Anon_607,r_608>@M[Orig] * r_608::cll<p_611,n_612>@M[Orig][LHSCase]&flted_11_606+1=n & x'!=p & p_605=p & x'=x & h'=h & h=p & x'!=h' & !(v_bool_31_570') & x'!=h' & !(v_bool_31_570') & p_611=p_605 & n_612=flted_11_606 & 0<=flted_11_606 & A(n_625,n_612) & n_31'=1+n_625&{FLOW,(22,23)=__norm})[]
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop

 ]

!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::cll<p,n>@M[Orig][LHSCase]&h=p&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::
                                EXISTS(p_29,
                                n_30: x::cll<p_29,n_30>@M[Orig][LHSCase]&
                                A(res,n) & p_29=p & n_30=n&
                                {FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::cll<p,n>@M[Orig][LHSCase]&
                  h=p&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 66::
                              EXISTS(p_29,
                              n_30: x::cll<p_29,n_30>@M[Orig][LHSCase]&
                              p_29=p & n_30=n & n>=0 & n=res&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (res=n_632+1 & n_612=n-1 & 1<=n & A(n_632,n_612)) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node~node SUCCESS

Termination checking result:

Stop Omega... 99 invocations 
0 false contexts at: ()

Total verification time: 0.35 second(s)
	Time spent in main process: 0.28 second(s)
	Time spent in child processes: 0.07 second(s)
