Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_557#loop$int -> [ true -> Term_561[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_556,
 1<=x -> UNK_557#loop$int; [
 1<=x -> UNK_558#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_556,
 1<=x -> [
 1<=x -> UNK_558#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_558#loop$int -> [ true -> Term_563[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_556,
 1<=x -> [
 1<=x -> UNK_558#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_556,
 1<=x -> [
 1<=x -> Term_563[ x-0]]]
!!! 
Stop Omega... 55 invocations 
3 false contexts at: ( (9,10)  (9,8)  (9,3) )

Total verification time: 0.084003 second(s)
	Time spent in main process: 0.060003 second(s)
	Time spent in child processes: 0.024 second(s)
