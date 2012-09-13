Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_581#loop$int -> Loop_588,
UNK_582#loop$int -> [ true -> Term_590[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_580,
 3<=x -> UNK_581#loop$int; [
 3<=x & x<=4 -> UNK_583#loop$int,
 5<=x -> UNK_585#loop$int],
 1<=x & x<=2 -> UNK_582#loop$int; [
 1<=x & x<=2 -> UNK_584#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_580,
 3<=x -> Loop_588,
 1<=x & x<=2 -> [
 1<=x & x<=2 -> UNK_584#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_588 -> Loop_591,
UNK_584#loop$int -> Loop_592]
!!! Termination Spec:[
 x<=0 -> Term_580,
 3<=x -> Loop_588,
 1<=x & x<=2 -> [
 1<=x & x<=2 -> UNK_584#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_580,
 3<=x -> Loop_588,
 1<=x & x<=2 -> [
 1<=x & x<=2 -> Loop_592]]
!!! 
Stop Omega... 90 invocations 
0 false contexts at: ()

Total verification time: 0.112006 second(s)
	Time spent in main process: 0.076004 second(s)
	Time spent in child processes: 0.036002 second(s)
