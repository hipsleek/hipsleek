Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_544#loop$int~int~int -> [ y<=(0-1) & z<=0 -> Term_552[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> UNK_544#loop$int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> UNK_555#loop$int~int~int,
 0<=y -> UNK_553#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_554#loop$int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_555#loop$int~int~int -> [ true -> Term_562[ x-0]],
UNK_554#loop$int~int~int -> [ true -> Term_563[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> UNK_555#loop$int~int~int,
 0<=y -> UNK_553#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_554#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> UNK_553#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_564#loop$int~int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
UNK_553#loop$int~int~int -> [ z<=(0-1) -> Term_578[ y-(0-1)]],
UNK_564#loop$int~int~int -> [ true -> Term_579[ x-0]],
UNK_564#loop$int~int~int -> [ true -> Term_580[ z-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> UNK_553#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_564#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> UNK_582#loop$int~int~int,
 0<=z -> UNK_581#loop$int~int~int],
 y<=(0-1) & 1<=z -> UNK_583#loop$int~int~int]]
!!! 

!!! ROUND 4
!!! SUBST:[
UNK_582#loop$int~int~int -> [ true -> Term_593[ y-(0-1)]],
UNK_583#loop$int~int~int -> [ true -> Term_594[ x-0]],
UNK_583#loop$int~int~int -> [ true -> Term_595[ z-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> UNK_582#loop$int~int~int,
 0<=z -> UNK_581#loop$int~int~int],
 y<=(0-1) & 1<=z -> UNK_583#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> Term_593[ y-(0-1)],
 0<=z -> UNK_581#loop$int~int~int],
 y<=(0-1) & 1<=z -> UNK_596#loop$int~int~int]]
!!! 

!!! ROUND 5
!!! SUBST:[
UNK_581#loop$int~int~int -> [ true -> Term_606[ z-(0-1)]],
UNK_596#loop$int~int~int -> [ true -> Term_607[ x-0]],
UNK_596#loop$int~int~int -> [ true -> Term_608[ z-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> Term_593[ y-(0-1)],
 0<=z -> UNK_581#loop$int~int~int],
 y<=(0-1) & 1<=z -> UNK_596#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> Term_593[ y-(0-1)],
 0<=z -> Term_606[ z-(0-1)]],
 y<=(0-1) & 1<=z -> UNK_609#loop$int~int~int]]
!!! 

!!! ROUND 6
!!! SUBST:[
UNK_609#loop$int~int~int -> [ true -> Term_619[ x-0]],
UNK_609#loop$int~int~int -> [ true -> Term_620[ z-0]],
UNK_609#loop$int~int~int -> [ true -> Term_621[ 0-y]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> Term_593[ y-(0-1)],
 0<=z -> Term_606[ z-(0-1)]],
 y<=(0-1) & 1<=z -> UNK_609#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_562[ x-0],
 0<=y -> [
 z<=(0-1) -> Term_593[ y-(0-1)],
 0<=z -> Term_606[ z-(0-1)]],
 y<=(0-1) & 1<=z -> Term_619[ x-0]]]
!!! 
Stop Omega... 139 invocations 
0 false contexts at: ()

Total verification time: 0.196011 second(s)
	Time spent in main process: 0.096005 second(s)
	Time spent in child processes: 0.100006 second(s)
