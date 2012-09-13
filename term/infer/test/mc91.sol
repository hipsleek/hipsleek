Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure mc91$int... 
Procedure mc91$int SUCCESS

Termination checking result:

Termination Inference for mc91$int

!!! ROUND 1
!!! SUBST:[
UNK_571#mc91$int -> [ true -> Term_576[ 101-n]]]
!!! Termination Spec:[
 101<=n -> Term_570,
 n<=100 -> UNK_571#mc91$int; [
 90<=n & n<=100 -> UNK_572#mc91$int,
 n<=89 -> UNK_573#mc91$int]]
!!! 

!!! Inferred Termination Spec:[
 101<=n -> Term_570,
 n<=100 -> [
 90<=n & n<=100 -> UNK_572#mc91$int,
 n<=89 -> UNK_573#mc91$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_572#mc91$int -> [ true -> Term_578[ 101-n]]]
!!! Termination Spec:[
 101<=n -> Term_570,
 n<=100 -> [
 90<=n & n<=100 -> UNK_572#mc91$int,
 n<=89 -> UNK_573#mc91$int]]
!!! 

!!! Inferred Termination Spec:[
 101<=n -> Term_570,
 n<=100 -> [
 90<=n & n<=100 -> Term_578[ 101-n],
 n<=89 -> UNK_573#mc91$int]]
!!! 

!!! ROUND 3
!!! SUBST:[
UNK_573#mc91$int -> [ true -> Term_580]]
!!! Termination Spec:[
 101<=n -> Term_570,
 n<=100 -> [
 90<=n & n<=100 -> Term_578[ 101-n],
 n<=89 -> UNK_573#mc91$int]]
!!! 

!!! Inferred Termination Spec:[
 101<=n -> Term_570,
 n<=100 -> [
 90<=n & n<=100 -> Term_578[ 101-n],
 n<=89 -> Term_580]]
!!! 
Stop Omega... 80 invocations 
10 false contexts at: ( (7,14)  (7,23)  (7,21)  (10,2)  (10,9)  (9,10)  (9,17)  (9,15)  (9,6)  (8,6) )

Total verification time: 0.068002 second(s)
	Time spent in main process: 0.052002 second(s)
	Time spent in child processes: 0.016 second(s)
