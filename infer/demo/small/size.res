
!!! Full processing file (parse only) "infer/demo/small/size.ss"
!!!  processing primitives "["prelude.ss"]
!!! Full processing file "infer/demo/small/size.ss"
!!!  processing primitives "["prelude.ss"]Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! TRANSLATED SPECS: EInfer [R_635,R_636]
   EBase exists (Expl)(Impl)[n_632; 
         n_633](ex)x::llN<n_632>@M[0][Orig][LHSCase] * 
         y::llN<n_633>@M[0][Orig][LHSCase]&x!=null & R_635(n_632,n_633)&
         {FLOW,(22,23)=__norm}[]
           EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                   EAssume 82::
                     EXISTS(n_634: x::llN<n_634>@M[0][Orig][LHSCase]&
                     R_636(n_632,n_633,n_634)&{FLOW,(22,23)=__norm})[]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_635: ( R_635(n_632,n_670) & 2<=n_632 & n_669=n_632-1 & 0<=n_670) -->  R_635(n_669,n_670),
RELDEFN R_636: ( n_632=1 & n_634=n_633+1 & 0<=n_633 & R_635(n_632,n_633)) -->  R_636(n_632,n_633,n_634),
RELDEFN R_636: ( R_636(n_669,n_633,n_688) & 0<=n_669 & n_632=n_669+1 & n_688=n_634-1 & 
0<=n_633 & 2<=n_634 & R_635(n_632,n_633)) -->  R_636(n_632,n_633,n_634)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R_636(n_632,n_633,n_634), n_632=n_634-n_633 & 0<=n_633 & n_633<n_634, R_635(n_632,n_633), true)]
*************************************

!!! REL POST :  R_636(n_632,n_633,n_634)
!!! POST:  n_632=n_634-n_633 & 0<=n_633 & n_633<n_634
!!! REL PRE :  R_635(n_632,n_633)
!!! PRE :  true
Procedure append$node~node SUCCESS

Checking procedure copy$node... 
!!! TRANSLATED SPECS: EInfer [R_707,R_708]
   EBase exists (Expl)(Impl)[n_704](ex)x::llN<n_704>@M[0][Orig][LHSCase]&
         R_707(n_704)&{FLOW,(22,23)=__norm}[]
           EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                   EAssume 85::
                     EXISTS(n_705,n_706: x::llN<n_705>@M[0][Orig][LHSCase] * 
                     res::llN<n_706>@M[0][Orig][LHSCase]&
                     R_708(n_704,n_705,n_706)&{FLOW,(22,23)=__norm})[]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_707: ( R_707(n_704) & 1<=n_704 & n_731=n_704-1) -->  R_707(n_731),
RELDEFN R_708: ( R_708(n_731,n_744,n_745) & 0<=n_744 & 0<=n_745 & n_731=n_704-1 & 
n_706=n_745+1 & n_705=n_744+1 & 1<=n_704 & R_707(n_704)) -->  R_708(n_704,n_705,n_706),
RELDEFN R_708: ( n_704=0 & n_705=0 & n_706=0 & R_707(n_704)) -->  R_708(n_704,n_705,n_706)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R_636(n_632,n_633,n_634), n_632=n_634-n_633 & 0<=n_633 & n_633<n_634, R_635(n_632,n_633), true),
( R_708(n_704,n_705,n_706), n_705=n_706 & n_704=n_706 & 0<=n_706, R_707(n_704), true)]
*************************************

!!! REL POST :  R_708(n_704,n_705,n_706)
!!! POST:  n_705=n_706 & n_704=n_706 & 0<=n_706
!!! REL PRE :  R_707(n_704)
!!! PRE :  true
Procedure copy$node SUCCESS

Checking procedure del_index$node~int... 
!!! TRANSLATED SPECS: EInfer [R_784,R_785]
   EBase exists (Expl)(Impl)[n_782](ex)x::llN<n_782>@M[0][Orig][LHSCase]&
         R_784(n_782,i)&{FLOW,(22,23)=__norm}[]
           EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                   EAssume 88::
                     EXISTS(n_783: x::llN<n_783>@M[0][Orig][LHSCase]&
                     R_785(n_782,n_783,i)&{FLOW,(22,23)=__norm})[]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_784: ( 2<=i & 1<=n_782 & R_784(n_782,i) & v_int_51_595'=i-1 & n_859=n_782-1) -->  R_784(n_859,v_int_51_595'),
RELDEFN R_784: ( 1<=n_782 & i<=0 & R_784(n_782,i) & v_int_51_595'=i-1 & n_859=n_782-1) -->  R_784(n_859,v_int_51_595'),
RELASS [R_784]: ( R_784(n_782,i)) -->  (n_782!=0 | 2>i) & (n_782!=0 | i>0),
RELASS [R_784]: ( R_784(n_782,i)) -->  n_782!=0 | i!=1,
RELASS [R_784]: ( R_784(n_782,i)) -->  n_782!=0 | i!=1,
RELASS [R_784]: ( R_784(n_782,i)) -->  n_782!=1 | i!=1,
RELDEFN R_785: ( i=1 & n_783=n_782-1 & 2<=n_782 & R_784(n_782,i)) -->  R_785(n_782,n_783,i),
RELDEFN R_785: ( 1<=v_int_51_879 & 0<=n_878 & R_785(n_859,n_878,v_int_51_879) & 
R_784(n_782,i) & n_859=n_782-1 & i=v_int_51_879+1 & n_783=n_878+1 & 1<=n_782) -->  R_785(n_782,n_783,i),
RELDEFN R_785: ( 0<=n_878 & v_int_51_879<=(0-1) & R_785(n_859,n_878,v_int_51_879) & 
R_784(n_782,i) & n_859=n_782-1 & i=v_int_51_879+1 & n_783=n_878+1 & 1<=n_782) -->  R_785(n_782,n_783,i)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R_708(n_704,n_705,n_706), n_705=n_706 & n_704=n_706 & 0<=n_706, R_707(n_704), true),
( R_636(n_632,n_633,n_634), n_632=n_634-n_633 & 0<=n_633 & n_633<n_634, R_635(n_632,n_633), true),
( R_785(n_782,i,n_783), n_782=n_783+1 & 1<=i & i<=n_783, R_784(n_782,i), 1<=i & i<n_782)]
*************************************

!!! REL POST :  R_785(n_782,i,n_783)
!!! POST:  n_782=n_783+1 & 1<=i & i<=n_783
!!! REL PRE :  R_784(n_782,i)
!!! PRE :  1<=i & i<n_782
Procedure del_index$node~int SUCCESS

Checking procedure del_val$node~int... 
!!! TRANSLATED SPECS: EInfer [R_898,R_899]
   EBase exists (Expl)(Impl)[n_896](ex)x::llN<n_896>@M[0][Orig][LHSCase]&
         R_898(n_896,a)&{FLOW,(22,23)=__norm}[]
           EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                   EAssume 93::
                     EXISTS(n_897: res::llN<n_897>@M[0][Orig][LHSCase]&
                     R_899(n_896,n_897,a)&{FLOW,(22,23)=__norm})[]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_898: ( 1<=n_896 & n_938=n_896-1 & R_898(n_896,a')) -->  R_898(n_938,a'),
RELDEFN R_899: ( n_896=0 & n_897=0 & R_898(n_896,a)) -->  R_899(n_896,n_897,a),
RELDEFN R_899: ( n_897=n_896-1 & 1<=n_896 & R_898(n_896,a)) -->  R_899(n_896,n_897,a),
RELDEFN R_899: ( 0<=n_950 & n_938=n_896-1 & n_897=n_950+1 & 1<=n_896 & R_898(n_896,a) & 
R_899(n_938,n_950,a)) -->  R_899(n_896,n_897,a)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R_785(n_782,i,n_783), n_782=n_783+1 & 1<=i & i<=n_783, R_784(n_782,i), 1<=i & i<n_782),
( R_636(n_632,n_633,n_634), n_632=n_634-n_633 & 0<=n_633 & n_633<n_634, R_635(n_632,n_633), true),
( R_708(n_704,n_705,n_706), n_705=n_706 & n_704=n_706 & 0<=n_706, R_707(n_704), true),
( R_899(n_896,a,n_897), 0<=n_897 & (n_896-1)<=n_897 & n_897<=n_896, R_898(n_896,a), true)]
*************************************

!!! REL POST :  R_899(n_896,a,n_897)
!!! POST:  0<=n_897 & (n_896-1)<=n_897 & n_897<=n_896
!!! REL PRE :  R_898(n_896,a)
!!! PRE :  true
Procedure del_val$node~int SUCCESS

Checking procedure insert$node~int... 
!!! TRANSLATED SPECS: EInfer [R_975,R_976]
   EBase exists (Expl)(Impl)[n_973](ex)x::llN<n_973>@M[0][Orig][LHSCase]&
         x!=null & R_975(n_973,a)&{FLOW,(22,23)=__norm}[]
           EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                   EAssume 97::
                     EXISTS(n_974: x::llN<n_974>@M[0][Orig][LHSCase]&
                     R_976(n_973,n_974,a)&{FLOW,(22,23)=__norm})[]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_975: ( n_973=n_1011+1 & 1<=n_1011 & R_975(n_973,a')) -->  R_975(n_1011,a'),
RELDEFN R_976: ( n_974=2 & n_973=1 & R_975(n_973,a)) -->  R_976(n_973,n_974,a),
RELDEFN R_976: ( 0<=n_1011 & n_973=n_1011+1 & n_1036=n_974-1 & 2<=n_974 & R_975(n_973,a) & 
R_976(n_1011,n_1036,a)) -->  R_976(n_973,n_974,a)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R_899(n_896,a,n_897), 0<=n_897 & (n_896-1)<=n_897 & n_897<=n_896, R_898(n_896,a), true),
( R_708(n_704,n_705,n_706), n_705=n_706 & n_704=n_706 & 0<=n_706, R_707(n_704), true),
( R_636(n_632,n_633,n_634), n_632=n_634-n_633 & 0<=n_633 & n_633<n_634, R_635(n_632,n_633), true),
( R_785(n_782,i,n_783), n_782=n_783+1 & 1<=i & i<=n_783, R_784(n_782,i), 1<=i & i<n_782),
( R_976(n_973,a,n_974), n_973=n_974-1 & 2<=n_974, R_975(n_973,a), true)]
*************************************

!!! REL POST :  R_976(n_973,a,n_974)
!!! POST:  n_973=n_974-1 & 2<=n_974
!!! REL PRE :  R_975(n_973,a)
!!! PRE :  true
Procedure insert$node~int SUCCESS

Checking procedure traverse$node... 
!!! TRANSLATED SPECS: EInfer [R_1054,R_1055]
   EBase exists (Expl)(Impl)[n_1052](ex)x::llN<n_1052>@M[0][Orig][LHSCase]&
         R_1054(n_1052)&{FLOW,(22,23)=__norm}[]
           EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                   EAssume 100::
                     EXISTS(n_1053: x::llN<n_1053>@M[0][Orig][LHSCase]&
                     R_1055(n_1052,n_1053)&{FLOW,(22,23)=__norm})[]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_1054: ( R_1054(n_1052) & 1<=n_1052 & n_1079=n_1052-1) -->  R_1054(n_1079),
RELDEFN R_1055: ( R_1055(n_1079,n_1085) & 0<=n_1085 & n_1079=n_1052-1 & n_1053=n_1085+1 & 
1<=n_1052 & R_1054(n_1052)) -->  R_1055(n_1052,n_1053),
RELDEFN R_1055: ( n_1052=0 & n_1053=0 & R_1054(n_1052)) -->  R_1055(n_1052,n_1053)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R_976(n_973,a,n_974), n_973=n_974-1 & 2<=n_974, R_975(n_973,a), true),
( R_785(n_782,i,n_783), n_782=n_783+1 & 1<=i & i<=n_783, R_784(n_782,i), 1<=i & i<n_782),
( R_636(n_632,n_633,n_634), n_632=n_634-n_633 & 0<=n_633 & n_633<n_634, R_635(n_632,n_633), true),
( R_708(n_704,n_705,n_706), n_705=n_706 & n_704=n_706 & 0<=n_706, R_707(n_704), true),
( R_899(n_896,a,n_897), 0<=n_897 & (n_896-1)<=n_897 & n_897<=n_896, R_898(n_896,a), true),
( R_1055(n_1052,n_1053), n_1052=n_1053 & 0<=n_1052, R_1054(n_1052), true)]
*************************************

!!! REL POST :  R_1055(n_1052,n_1053)
!!! POST:  n_1052=n_1053 & 0<=n_1052
!!! REL PRE :  R_1054(n_1052)
!!! PRE :  true
Procedure traverse$node SUCCESS

Termination checking result:

Stop Omega... 454 invocations 
0 false contexts at: ()

Total verification time: 1.58 second(s)
	Time spent in main process: 0.94 second(s)
	Time spent in child processes: 0.64 second(s)

