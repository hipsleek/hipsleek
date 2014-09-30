
Processing file "qsort-tail.ss"
Parsing qsort-tail.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure partition1$node~node~node~node~int... 
Procedure partition1$node~node~node~node~int SUCCESS
Checking procedure qsort$node~node... 
assert:qsort-tail.ss:76: 2:  : ok


assert:qsort-tail.ss:77: 2:  : ok


dprint: qsort-tail.ss:78: ctx:  List of Failesc Context: [FEC(0, 1, 1  [(135::,1 ); (135::,1 ); (134::,1 ); (134::,1 )])]

Successful States:
[
 Label: [(135::,1 ); (135::,1 ); (134::,1 ); (134::,1 )]
 State:x'::node<d_1890,p_1891>@M[Orig][] * p_1891::bnd_tail<flted_42_1889,t_1886,sm_1887,lg_1888>@M[Orig]@ rem br[{225,224}] & (([
                                                                    0!=flted_42_1889 & 
                                                                    0<=flted_42_1889 & 
                                                                    1+
                                                                    flted_42_1889=n & 
                                                                    0!=n & 
                                                                    0<=n]
                                                                    [null!=p_1891]
                                                                    [tx=tx' & 
                                                                    tx=tx_1850 & 
                                                                    tx=t_1886]
                                                                    [d_1890=temp_77' & 
                                                                    lg=lg_1888 & 
                                                                    sm=sm_1887 & 
                                                                    sm<=d_1890 & 
                                                                    d_1890<=lg]
                                                                    [x=x' & 
                                                                    null!=x]
                                                                    [!(v_bool_67_783')]
                                                                    [!(v_bool_68_782')]
                                                                    )) & {FLOW,(20,21)=__norm}
 ]

assert:qsort-tail.ss:93: 12:  : ok


assert:qsort-tail.ss:100: 12:  : ok

[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 
[add_perm_to_struc_formula] Warning: rhs_p for ECase not added 

Procedure qsort$node~node SUCCESS
Stop Omega... 7647 invocations 
1 false contexts at: ( (67,16) )

Total verification time: 26.969684 second(s)
	Time spent in main process: 18.525157 second(s)
	Time spent in child processes: 8.444527 second(s)
