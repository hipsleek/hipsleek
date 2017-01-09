
Processing file "vperm4.ss"
Parsing vperm4.ss ...
Parsing ../../../../prelude_vp.ss ...
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure inc$int~int... 
Procedure inc$int~int SUCCESS
Checking procedure testjoin$int~int... 
Procedure testjoin$int~int SUCCESS
Checking procedure main$... 
dprint: vperm4.ss:38: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & y_24'=y_575 & x_574=0 & y_575=1 & id_22'=tid_573 & {FLOW,(20,21)=__norm}
AND  <thread=tid_573>  <ref:x_23> true & @full[x_23] & x_23'=y_575+x_574
         es_var_zero_perm: [x_23']

 ]

dprint: vperm4.ss:41: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & y_575+x_574=i & y_24'=y_575 & x_574=0 & y_575=1 & id_22'=tid_573 & x_23'=i & {FLOW,(20,21)=__norm}[]

 ]

Procedure main$ SUCCESS
Stop Omega... 37 invocations 
0 false contexts at: ()

Total verification time: 0.17 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.02 second(s)
