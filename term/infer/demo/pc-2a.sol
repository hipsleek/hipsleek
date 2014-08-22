Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_543#loop$int~int -> [ x<=((0-y)-1) -> Term_550[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> UNK_543#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> UNK_552#loop$int~int,
 0<=(x+y) -> UNK_551#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_552#loop$int~int -> [ true -> Term_555[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> UNK_552#loop$int~int,
 0<=(x+y) -> UNK_551#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> Term_555[ x-0],
 0<=(x+y) -> UNK_551#loop$int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
UNK_551#loop$int~int -> [ 1<=(x+y) -> Loop_562, x<=(0-y) -> Term_563[ x-((0-y)-1)]]]
!!! Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> Term_555[ x-0],
 0<=(x+y) -> UNK_551#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> Term_555[ x-0],
 0<=(x+y) -> [
 1<=(x+y) -> Loop_562,
 x<=(0-y) -> UNK_564#loop$int~int]]]
!!! 

!!! ROUND 4
!!! SUBST:[
UNK_564#loop$int~int -> [ true -> Term_567]]
!!! Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> Term_555[ x-0],
 0<=(x+y) -> [
 1<=(x+y) -> Loop_562,
 x<=(0-y) -> UNK_564#loop$int~int]]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_542,
 1<=x -> [
 x<=((0-y)-1) -> Term_555[ x-0],
 0<=(x+y) -> [
 1<=(x+y) -> Loop_562,
 x<=(0-y) -> Term_567]]]
!!! 
Stop Omega... 89 invocations 
0 false contexts at: ()

Total verification time: 0.128006 second(s)
	Time spent in main process: 0.080004 second(s)
	Time spent in child processes: 0.048002 second(s)
