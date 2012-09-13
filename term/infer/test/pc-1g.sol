Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1Starting Reduce... 
Halting Reduce... 
Starting mathematica... 
Mathematica started successfully!
Halting mathematica... 

!!! SUBST:[
UNK_543#loop$int~int -> [ x<=(0-y) -> Term_552, 1<=(x+y) -> Term_553[ 0+(1*y)+(2*x)]]]
!!! Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> UNK_543#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=(0-y) -> Term_552,
 1<=(x+y) -> Term_553[ 0+(1*y)+(2*x)]]]
!!! 
Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.472028 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.408025 second(s)
