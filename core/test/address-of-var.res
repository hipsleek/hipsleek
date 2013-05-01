Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure inc$int_ptr... 
Procedure inc$int_ptr SUCCESS

Checking procedure address_of_global$int... 
assert:address-of-var.ss:41: 2:  : ok


Procedure address_of_global$int SUCCESS

Checking procedure address_of_global2$int_ptr~int... 
assert:address-of-var.ss:52: 2:  : ok


Procedure address_of_global2$int_ptr~int SUCCESS

Checking procedure address_of_local$... 
assert:address-of-var.ss:30: 2:  : ok


Procedure address_of_local$ SUCCESS

Checking procedure address_of_param$int... 
assert:address-of-var.ss:19: 2:  : ok


Procedure address_of_param$int SUCCESS

Termination checking result:

Stop Omega... 33 invocations 
0 false contexts at: ()

Total verification time: 0.23 second(s)
	Time spent in main process: 0.21 second(s)
	Time spent in child processes: 0.02 second(s)
