Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_560#loop$int -> [ true -> Term_565[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_559,
 1<=x -> UNK_560#loop$int; [
 x=1 -> UNK_561#loop$int,
 2<=x -> UNK_562#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_559,
 1<=x -> [
 x=1 -> UNK_561#loop$int,
 2<=x -> UNK_562#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_562#loop$int -> Loop_566,
UNK_561#loop$int -> Loop_567]
!!! Termination Spec:[
 x<=0 -> Term_559,
 1<=x -> [
 x=1 -> UNK_561#loop$int,
 2<=x -> UNK_562#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_559,
 1<=x -> [
 x=1 -> Loop_567,
 2<=x -> Loop_566]]
!!! 
Stop Omega... 64 invocations 
0 false contexts at: ()

Total verification time: 0.092005 second(s)
	Time spent in main process: 0.064004 second(s)
	Time spent in child processes: 0.028001 second(s)
