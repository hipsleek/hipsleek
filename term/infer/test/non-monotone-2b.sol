Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_534#loop$int -> [ 5<=x -> Term_542]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> UNK_534#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> UNK_543#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_543#loop$int -> [ x<=2 -> Term_551]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> UNK_543#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> [
 x<=2 -> Term_551,
 3<=x -> UNK_552#loop$int]]]
!!! 

!!! ROUND 3
!!! SUBST:[
UNK_552#loop$int -> [ 4<=x -> Term_560]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> [
 x<=2 -> Term_551,
 3<=x -> UNK_552#loop$int]]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> [
 x<=2 -> Term_551,
 3<=x -> [
 4<=x -> Term_560,
 x<=3 -> UNK_561#loop$int]]]]
!!! 

!!! ROUND 4
!!! SUBST:[
UNK_561#loop$int -> [ true -> Term_563]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> [
 x<=2 -> Term_551,
 3<=x -> [
 4<=x -> Term_560,
 x<=3 -> UNK_561#loop$int]]]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 5<=x -> Term_542,
 x<=4 -> [
 x<=2 -> Term_551,
 3<=x -> [
 4<=x -> Term_560,
 x<=3 -> Term_563]]]]
!!! 
Stop Omega... 103 invocations 
0 false contexts at: ()

Total verification time: 0.104005 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.040002 second(s)
