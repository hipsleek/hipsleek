
Processing file "alt_threading1.ss"
Parsing alt_threading1.ss ...
Parsing ../../../../prelude_vp.ss ...
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure increment$cell... 
Procedure increment$cell SUCCESS
Checking procedure main$... 
dprint: alt_threading1.ss:34: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & i=n_22' & id_23'=tid_629 & {FLOW,(20,21)=__norm}
AND  <thread=tid_629>  <ref:x_21> x_21'::cell<flted_12_605>@M[Orig] & flted_12_605=1+i & @full[x_21]
         es_var_zero_perm: [x_21']

 ]

assert:alt_threading1.ss:38: 2:  : ok


Procedure main$ SUCCESS
Stop Omega... 34 invocations 
0 false contexts at: ()

Total verification time: 0.18 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.02 second(s)
