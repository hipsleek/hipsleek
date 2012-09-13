Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_535#loop$int~int -> [ y<=(0-1) -> Term_549[ x-0]],
UNK_536#loop$int~int -> [ y<=0 -> Loop_550]]
!!! Termination Spec:[
 x=0 -> Term_534,
 1<=x -> UNK_535#loop$int~int,
 x<=(0-1) -> UNK_536#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> UNK_552#loop$int~int,
 0<=y -> UNK_551#loop$int~int],
 x<=(0-1) -> [
 y<=0 -> Loop_550,
 1<=y -> UNK_553#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_550 -> Loop_554,
UNK_552#loop$int~int -> [ true -> Term_559[ x-0]],
UNK_553#loop$int~int -> [ true -> Term_560[ 0-(x-0)]]]
!!! Termination Spec:[
 x=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> UNK_552#loop$int~int,
 0<=y -> UNK_551#loop$int~int],
 x<=(0-1) -> [
 y<=0 -> Loop_550,
 1<=y -> UNK_553#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> MayLoop_561,
 0<=y -> UNK_551#loop$int~int],
 x<=(0-1) -> [
 y<=0 -> Loop_550,
 1<=y -> MayLoop_562]]
!!! 

!!! ROUND 3
!!! SUBST:[
MayLoop_561 -> MayLoop_563,
UNK_551#loop$int~int -> MayLoop_564]
!!! Termination Spec:[
 x=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> MayLoop_561,
 0<=y -> UNK_551#loop$int~int],
 x<=(0-1) -> [
 y<=0 -> Loop_550,
 1<=y -> MayLoop_562]]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> MayLoop_561,
 0<=y -> MayLoop_564],
 x<=(0-1) -> [
 y<=0 -> Loop_550,
 1<=y -> MayLoop_562]]
!!! 
Stop Omega... 96 invocations 
0 false contexts at: ()

Total verification time: 0.19601 second(s)
	Time spent in main process: 0.088004 second(s)
	Time spent in child processes: 0.108006 second(s)
