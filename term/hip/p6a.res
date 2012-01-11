
Processing file "infer-6a.ss"
Parsing infer-6a.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS
Checking procedure f$int~int~int... 
Procedure f$int~int~int SUCCESS

Termination checking result:
(33)->(42) (ERR: not decreasing) Term[0; pv_488; 0 - x]->Term[0; pv_488; 0 - x']
(33)->(42) (ERR) Term[0; pv_488; 0 - x]->Loop

Stop Omega... 156 invocations 
9 false contexts at: ( (42,1)  (38,1)  (40,2)  (40,14)  (40,9)  (40,6)  (39,6)  (39,2)  (39,2) )

Total verification time: 0.29 second(s)
	Time spent in main process: 0.24 second(s)
	Time spent in child processes: 0.05 second(s)
