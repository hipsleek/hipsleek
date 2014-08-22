Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_535#loop$int~int -> [ y<=(0-1) -> Term_542[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> UNK_535#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> UNK_544#loop$int~int,
 0<=y -> UNK_543#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_544#loop$int~int -> [ true -> Term_547[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> UNK_544#loop$int~int,
 0<=y -> UNK_543#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> Term_547[ x-0],
 0<=y -> UNK_543#loop$int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
UNK_543#loop$int~int -> [ true -> Term_550[ y-(0-1)]]]
!!! Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> Term_547[ x-0],
 0<=y -> UNK_543#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 y<=(0-1) -> Term_547[ x-0],
 0<=y -> Term_550[ y-(0-1)]]]
!!! 
Stop Omega... 66 invocations 
0 false contexts at: ()

Total verification time: 0.092004 second(s)
	Time spent in main process: 0.068004 second(s)
	Time spent in child processes: 0.024 second(s)
