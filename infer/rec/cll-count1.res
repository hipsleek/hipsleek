
Processing file "cll-count1.ss"
Parsing cll-count1.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure count$node~node... 
dprint: cll-count1.ss:32: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(60::,0 ); (60::,0 )])]

Successful States:
[
 Label: [(60::,0 ); (60::,0 )]
 State:x::cll<p,n>@M[Orig][LHSCase]&x'=x & h'=h & h=p & x'=h' & v_bool_31_536' & x'=h' & v_bool_31_536'&{FLOW,(20,21)=__norm}
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop
 ]

dprint: cll-count1.ss:40: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(60::,1 ); (60::,1 )]) FEC(0, 0, 1  [(60::,1 ); (60::,1 )])]

Successful States:
[
 Label: [(60::,1 ); (60::,1 )]
 State:EXISTS(n_598: x'::node<Anon_573,r_574>@M[Orig] * r_574::cll<p_577,n_578>@M[Orig][LHSCase]&flted_11_572+1=n & x'!=p & p_571=p & x'=x & h'=h & h=p & x'!=h' & 138::!(v_bool_31_536') & x'!=h' & !(v_bool_31_536') & p_577=p_571 & n_578=flted_11_572 & 0<=flted_11_572 & A(n_598,n_578) & 0<=n_578 & n_32'=1+n_598&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop
 ],

Successful States:
[
 Label: [(60::,1 ); (60::,1 )]
 State:EXISTS(n_599: x'::node<Anon_573,r_574>@M[Orig] * r_574::cll<p_571,flted_11_572>@M[Orig] * r_574::cll<p_577,n_578>@M[Orig][LHSCase]&flted_11_572+1=n & x'!=p & p_571=p & x'=x & h'=h & h=p & x'!=h' & 138::!(v_bool_31_536') & x'!=h' & !(v_bool_31_536') & p_571=p_577 & flted_11_572=n_578 & r_574=p_577 & n_578=0 & A(n_599,n_578) & 0<=n_578 & n_32'=1+n_599&{FLOW,(20,21)=__norm})
       es_infer_vars/rel: [A]
       es_var_measures: MayLoop
 ]

!!! REL :  A(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::cll<p,n>@M[Orig][LHSCase]&h=p&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(p_30,
                                n_31: x::cll<p_30,n_31>@M[Orig][LHSCase]&
                                A(res,n) & p_30=p & n_31=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n](ex)x::cll<p,n>@M[Orig][LHSCase]&
                  h=p&{FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::cll<p_30,n_31>@M[Orig][LHSCase]&p_30=p & 
                              n_31=n & n>=0 & n=res & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(flted_11_572:exists(n_31:(n_578=0 & n=1 | 1+n_578=n_31 & 1+
  flted_11_572=n_31 & n=n_31 & 2<=n_31) & A(n_611,n_578) & -1+
  res=n_611))) --> A(res,n),
 (exists(flted_11_572:exists(flted_11_620:(n_578=0 & n=1 | 
  n_578=flted_11_620 & flted_11_572=flted_11_620 & -1+n=flted_11_620 & 
  1<=flted_11_620) & A(n_611,n_578) & -1+res=n_611))) --> A(res,n),
 (res=0 & n=0) --> A(res,n),
 (A(n_640,n_578) & -1+res=n_640 & n=1 & n_578=0) --> A(res,n)]
!!! NEW ASSUME:[ RELASS [A]: ( A(n_611,n_578)) -->  n_578<=0]
!!! NEW RANK:[]
Procedure count$node~node SUCCESS

Termination checking result:

Stop Omega... 197 invocations 
0 false contexts at: ()

Total verification time: 1.88 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 1.45 second(s)
