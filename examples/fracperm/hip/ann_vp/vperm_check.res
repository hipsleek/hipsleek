
Processing file "vperm_check.ss"
Parsing vperm_check.ss ...
Parsing ../../../../prelude_vp.ss ...
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure inc$cell... 
Procedure inc$cell SUCCESS
Checking procedure inc$int... 
Procedure inc$int SUCCESS
Checking procedure test1$int~int... 
dprint: vperm_check.ss:33: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & x_659=x & y'=y & id_32'=tid_658 & {FLOW,(20,21)=__norm}
AND  <thread=tid_658>  <ref:x> true & @full[x]
         es_var_zero_perm: [x']

 ]

VarPerm Failure:vperm_check.ss:34: 2: check_full_varperm: var [x'] MUST have full permission


dprint:vperm_check.ss:35 empty/false context
Procedure test1$int~int result FAIL-1
Checking procedure test2$cell~cell... 
dprint: vperm_check.ss:48: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:x::cell<i>@M[Orig] * y::cell<j>@M[Orig] & x_664=x & y'=y & id_31'=tid_663 & {FLOW,(20,21)=__norm}
AND  <thread=tid_663>  <ref:x> true & @full[x]
         es_var_zero_perm: [x']

 ]

VarPerm Failure:vperm_check.ss:50: 2: check_full_varperm: var [x'] MUST have full permission


Procedure test2$cell~cell result FAIL-1
Checking procedure test3$int~int... 
dprint: vperm_check.ss:62: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & x_694=x & y'=y & id_26'=tid_693 & {FLOW,(20,21)=__norm}
AND  <thread=tid_693>  <ref:x> true & @full[x]
         es_var_zero_perm: [x']

 ]

VarPerm Failure:vperm_check.ss:63: 6: check_full_varperm: var [x'] MUST have full permission


Procedure test3$int~int result FAIL-1
Checking procedure test4$int~int... 
dprint: vperm_check.ss:76: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & x_699=x & y'=y & id_25'=tid_698 & {FLOW,(20,21)=__norm}
AND  <thread=tid_698>  <ref:x> true & @full[x]
         es_var_zero_perm: [x']

 ]

VarPerm Failure:vperm_check.ss:78: 9: check_full_varperm: var [x'] MUST have full permission


Procedure test4$int~int result FAIL-1
Stop Omega... 33 invocations 
0 false contexts at: ()

Total verification time: 0.19 second(s)
	Time spent in main process: 0.17 second(s)
	Time spent in child processes: 0.02 second(s)
