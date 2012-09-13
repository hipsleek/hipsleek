Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_548#loop$int -> [ true -> Term_552[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> UNK_548#loop$int; [
 1<=x & x<=2 -> UNK_549#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> [
 1<=x & x<=2 -> UNK_549#loop$int,
 3<=x -> UNK_553#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_553#loop$int -> Loop_554,
UNK_549#loop$int -> Loop_555]
!!! Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> [
 1<=x & x<=2 -> UNK_549#loop$int,
 3<=x -> UNK_553#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> [
 1<=x & x<=2 -> Loop_555,
 3<=x -> Loop_554]]
!!! 
Stop Omega... 63 invocations 
0 false contexts at: ()

Total verification time: 0.084003 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.02 second(s)
