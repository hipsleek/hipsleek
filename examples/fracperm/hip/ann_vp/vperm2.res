
Processing file "vperm2.ss"
Parsing vperm2.ss ...
Parsing ../../../../prelude_vp.ss ...
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure inc$int... 
Procedure inc$int SUCCESS
Checking procedure testfork$int~int... 
dprint: vperm2.ss:22: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & x_589=x & y'=y & id_26'=tid_588 & {FLOW,(20,21)=__norm}
AND  <thread=tid_588>  <ref:x> true & @full[x] & x'=1+x_589
         es_var_zero_perm: [x']

 ]

dprint: vperm2.ss:24: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & x_589=x & id_26'=tid_588 & y'=1+y & {FLOW,(20,21)=__norm}
AND  <thread=tid_588>  <ref:x> true & @full[x] & x'=1+x_589
         es_var_zero_perm: [x']

 ]

Procedure testfork$int~int SUCCESS
Checking procedure main$... 
dprint: vperm2.ss:50: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & y_25'=1+0 & {FLOW,(20,21)=__norm}
AND  <thread=id_23'>  <ref:> true & @full[x_24] & x_24'=1+0
         es_var_zero_perm: [x_24']

 ]

dprint: vperm2.ss:53: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & y_25'=1+0 & x_24'=1+0 & {FLOW,(20,21)=__norm}[]

 ]

Procedure main$ SUCCESS
Checking procedure testjoin$int~int... 
Procedure testjoin$int~int SUCCESS
Stop Omega... 40 invocations 
0 false contexts at: ()

Total verification time: 0.18 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.02 second(s)
