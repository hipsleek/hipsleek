Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node~node... 
dprint: cll-count1.ss:32: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(131::,0 ); (131::,0 )])]

Successful States:
[
 Label: [(131::,0 ); (131::,0 )]
 State:x::cll<p,n>@M[Orig][LHSCase]&x'=x & h'=h & h=p & x'=h' & v_bool_31_551' & x'=h' & v_bool_31_551'&{FLOW,(20,21)=__norm}[]
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop

 ]

dprint: cll-count1.ss:40: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(131::,1 ); (131::,1 )])]

Successful States:
[
 Label: [(131::,1 ); (131::,1 )]
 State:EXISTS(n_606: x'::node<Anon_588,r_589>@M[Orig] * r_589::cll<p_592,n_593>@M[Orig][LHSCase]&flted_11_587+1=n & x'!=p & p_586=p & x'=x & h'=h & h=p & x'!=h' & !(v_bool_31_551') & x'!=h' & !(v_bool_31_551') & p_592=p_586 & n_593=flted_11_587 & 0<=flted_11_587 & A(n_606,n_593) & n_34'=1+n_606&{FLOW,(20,21)=__norm})[]
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop

 ]

!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::cll<p,n>@M[Orig][LHSCase]&h=p&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 66::
                                EXISTS(p_32,
                                n_33: x::cll<p_32,n_33>@M[Orig][LHSCase]&
                                A(res,n) & p_32=p & n_33=n&
                                {FLOW,(20,21)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::cll<p,n>@M[Orig][LHSCase]&
                  h=p&{FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 66::
                              EXISTS(p_32,
                              n_33: x::cll<p_32,n_33>@M[Orig][LHSCase]&
                              p_32=p & n_33=n & n>=0 & n=res&
                              {FLOW,(20,21)=__norm})[])
!!! NEW RELS:[ (res=0 & n=0) --> A(res,n),
 (res=n_613+1 & n_593=n-1 & 1<=n & A(n_613,n_593)) --> A(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node~node SUCCESS

Termination checking result:

Stop Omega... 112 invocations 
0 false contexts at: ()

Total verification time: 0.34 second(s)
	Time spent in main process: 0.27 second(s)
	Time spent in child processes: 0.07 second(s)
