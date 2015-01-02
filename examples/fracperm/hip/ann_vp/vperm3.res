
Processing file "vperm3.ss"
Parsing vperm3.ss ...
Parsing ../../../../prelude_vp.ss ...
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo$int~int... 
Procedure foo$int~int SUCCESS
Checking procedure foo2$int~int... 
Procedure foo2$int~int SUCCESS
Checking procedure main$... 
dprint: vperm3.ss:25: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & i_630=0 & j_631=0 & k_30'=0 & id_27'=tid_629 & {FLOW,(20,21)=__norm}
AND  <thread=tid_629>  <ref:i_28,j_29> true & @full[i_28,j_29] & i_28'=1+i_630 & j_29'=1+j_631
         es_var_zero_perm: [i_28'; j_29']

 ]

dprint: vperm3.ss:27: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & i_630=0 & j_631=0 & k_30'=0 & id_27'=tid_629 & i_28'=1+i_630 & j_29'=1+j_631 & {FLOW,(20,21)=__norm}[]

 ]

assert:vperm3.ss:28: 2:  : ok


Procedure main$ SUCCESS
Checking procedure main2$... 
dprint: vperm3.ss:39: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & i_24'=i_644 & i_644=0 & j_643=0 & k_26'=0 & id_23'=tid_642 & {FLOW,(20,21)=__norm}
AND  <thread=tid_642>  <ref:j_25> true & @full[j_25] & j_25'=1+j_643
         es_var_zero_perm: [j_25']

 ]

dprint: vperm3.ss:41: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & i_24'=i_644 & i_644=0 & j_643=0 & k_26'=0 & id_23'=tid_642 & j_25'=1+j_643 & {FLOW,(20,21)=__norm}[]

 ]

assert:vperm3.ss:42: 2:  : ok


Procedure main2$ SUCCESS
Stop Omega... 38 invocations 
0 false contexts at: ()

Total verification time: 0.18 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.02 second(s)
