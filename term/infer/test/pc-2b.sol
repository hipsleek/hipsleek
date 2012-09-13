Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_541#loop$int~int -> [ 0<=(y+x) -> Loop_548, x<=((0-y)-1) -> Term_549[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_540,
 1<=x -> UNK_541#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_540,
 1<=x -> [
 0<=(y+x) -> Loop_548,
 x<=((0-y)-1) -> UNK_550#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_550#loop$int~int -> [ true -> Term_553[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_540,
 1<=x -> [
 0<=(y+x) -> Loop_548,
 x<=((0-y)-1) -> UNK_550#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_540,
 1<=x -> [
 0<=(y+x) -> Loop_548,
 x<=((0-y)-1) -> Term_553[ x-0]]]
!!! 
Stop Omega... 63 invocations 
0 false contexts at: ()

Total verification time: 0.072004 second(s)
	Time spent in main process: 0.052003 second(s)
	Time spent in child processes: 0.020001 second(s)
