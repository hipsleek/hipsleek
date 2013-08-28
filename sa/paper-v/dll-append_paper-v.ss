data node{
	node prev;
	node next;
}

dll<p> == self = null or self::node<p,x> * x::dll<self>;
	
PostPred G(node a,node b).
HeapPred H(node a,node b).

void dll_append(node x, node y)
//infer [H,G] requires H(x,y) ensures G(x,y);
requires x::dll<p> * y::dll<_> & x!=null &y!=null ensures x::dll<p>;
{
	if (x.next!=null) {
            dll_append(x.next,y);
            }
	else 
		{
			x.next = y;
			y.prev = x;
		}
}

/*
--pred-en-dangling

 H(x_833,y_834) ::=  
    x_833::node<__DP_H_9,next_15_798>@M * HP_800(next_15_798,y_834) * 
    y_834::node<__DP_H_2,__DP_H_3>@M,

 HP_800(next_15_831,y_832) ::=  
 emp&next_15_831=null
 or next_15_831::node<__DP_H_9,next_15_798>@M * HP_800(next_15_798,y_832)

 G(x_837,y_838) ::=  
 x_837::node<__DP_H_9,y_838>@M * y_838::node<x_837,__DP_H_3>@M
 or x_837::node<__DP_H_9,next_15_798>@M * G(next_15_798,y_838)&
    next_15_798!=null,



=====================
dll-append_paper.ss --classic --sa-en-eup
dll-append_paper.ss --classic --sa-dis-eup

gave the same result even though some predicates have been eliminated.
could we have the the --sa-dis-eup option working properly?


[ H(x_832,y_833) ::=  x_832::node<prev_15_797,next_15_798>@M * H_9(prev_15_797,y_833) * 
HP_800(next_15_798,y_833) * y_833::node<prev_21_828,next_21_829>@M * 
H_2(prev_21_828,x_832) * H_3(next_21_829,x_832),

 G(x_836,y_837) ::=  
 H_9(prev_15_797,y_837) * x_836::node<prev_15_797,next_15_798>@M * 
 G(next_15_798,y_837)&next_15_798!=null
 or H_9(prev_15_797,y_837) * x_836::node<prev_15_797,y_837>@M * 
    H_3(next_21_821,x_836) * y_837::node<x_836,next_21_821>@M,

 HP_800(next_15_830,y_831) ::=  
 next_15_830::node<prev_15_797,next_15_798>@M * H_9(prev_15_797,y_831) * 
 HP_800(next_15_798,y_831)
 or emp&next_15_830=null,

 H_9(prev_15_797,y) ::= NONE,
 H_2(prev_21_820,x) ::= NONE,
 H_3(next_21_821,x) ::= NONE]

dll-append_paper.ss --classic --sa-dis-eup

 H(x_832,y_833) ::=  x_832::node<prev_15_797,next_15_798>@M 
   * H_9(prev_15_797,y_833) * HP_800(next_15_798,y_833) 
   * y_833::node<prev_21_828,next_21_829>@M 
   * H_2(prev_21_828,x_832) * H_3(next_21_829,x_832),

 G(x_836,y_837) ::=  
 H_9(prev_15_797,y_837) * x_836::node<prev_15_797,next_15_798>@M * 
 G(next_15_798,y_837)&next_15_798!=null
 or H_9(prev_15_797,y_837) * x_836::node<prev_15_797,y_837>@M * 
    H_3(next_21_821,x_836) * y_837::node<x_836,next_21_821>@M,

 HP_800(next_15_830,y_831) ::=  
 next_15_830::node<prev_15_797,next_15_798>@M * H_9(prev_15_797,y_831) * 
 HP_800(next_15_798,y_831)
 or emp&next_15_830=null

 H_9(prev_15_797,y) ::= NONE,
 H_2(prev_21_820,x) ::= NONE,
 H_3(next_21_821,x) ::= NONE]


====

 G(x_843,y_844) ::=  x_843::node<prev_15_797,next_15_798>@M 
   * GP_845(next_15_798,y_844) * 
     H_3(next_21_821,x_843) * H_9(prev_15_797,y_844),
 
 GP_845(next_15_798,y_844) ::=  
 next_15_798::node<prev_15_853,next_15_851>@M * GP_845(next_15_851,y_844) * 
 H_3(next_21_852,next_15_798) * H_9(prev_15_853,y_844)
 or y_844::node<x_843,next_21_821>@M&next_15_798=y_844
 
==============================

Post-Check need to pick base cases ...
---------------
 id: 23; caller: []; line: 12; classic: false; kind: POST; hec_num: 5; evars: []; infer_vars: [H,G,HP_9,HP_0,HP_1,HP_2,HP_3]; c_heap: emp
 checkentail HP_9(next_15_797,y) * HP_0(prev_15_798,y) * 
x::node<y,prev_15_798>@M[Orig] * HP_2(next_21_820,x) * 
HP_3(prev_21_821,x) * y::node<next_21_820,x>@M[Orig]&next_15_797=null & 
!(v_bool_15_778') & next_15_797=null & !(v_bool_15_778') & 
next_15_797=next_20_817 & prev_21_821=prev_21_824&{FLOW,(22,23)=__norm}[]
 |-  G(x,y)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ HP_0(prev_15_798,y) * x::node<y,prev_15_798>@M * HP_2(next_21_820,x) * 
  y::node<next_21_820,x>@M&true --> G(x,y)&true]
res:  [
  HP_9(next_15_797,y) * HP_3(prev_21_821,x)&next_15_797=null & !(v_bool_15_778') & next_15_797=null & !(v_bool_15_778') & next_15_797=next_20_817 & prev_21_821=prev_21_824&{FLOW,(22,23)=__norm}[]
  ]

==============

[ H(x,y)&true --> x::node<next_15_797,prev_15_798>@M * 
  H_9(next_15_797,y@NI) * HP_800(prev_15_798,y@NI) * HP_801(y,x@NI)&true,

 H_9(next_15_797,y@NI) * HP_801(y,x@NI)&
  next_15_797!=null --> H(next_15_797,y)&true,

 HP_801(y,x@NI)&true --> y::node<next_21_820,prev_21_821>@M * 
  H_2(next_21_820,x@NI) * H_3(prev_21_821,x@NI)&true,

 HP_800(prev_15_798,y@NI) * x::node<next_15_797,prev_15_798>@M * 
  G(next_15_797,y)&next_15_797!=null --> G(x,y)&true,

 HP_800(prev_15_798,y@NI) * x::node<y,prev_15_798>@M * 
  H_2(next_21_820,x@NI) * y::node<next_21_820,x>@M&true --> G(x,y)&true]

=======

[ H(x,y) --> x::node<next_15_797,prev_15_798>@M * H_9(next_15_797,y@NI) * 
  HP_800(prev_15_798,y@NI) * HP_801(y,x@NI),

 H_9(next_15_797,y@NI) * HP_801(y,x@NI)&
  next_15_797!=null --> H(next_15_797,y),

 HP_801(y,x@NI) --> y::node<next_21_820,prev_21_821>@M * 
  H_2(next_21_820,x@NI) * H_3(prev_21_821,x@NI),

 HP_800(prev_15_798,y@NI) * x::node<next_15_797,prev_15_798>@M * 
  G(next_15_797,y)&next_15_797!=null --> G(x,y),

 H_3(prev_21_821,x@NI) --> emp,

 H_9(next_15_797,y@NI)&next_15_797=null --> emp,

 HP_800(prev_15_798,y@NI) * x::node<y,prev_15_798>@M * 
  H_2(next_21_820,x@NI) * y::node<next_21_820,x>@M --> G(x,y)]

==================
[ 

H(x_859,y_860) ::=  y_860::node<next_21_820,prev_21_821>@M * H_2(next_21_820,x_859) * 
  H_3(prev_21_821,x_859) * x_859::node<next_15_845,prev_15_846>@M * 
  HP_800(prev_15_846,y_860)&next_15_845=null,

 G(x_865,y_866) ::=  HP_800(prev_15_798,y_866) * x_865::node<next_15_797,prev_15_798>@M * 
      G(next_15_797,y_866)&next_15_797!=null
 or HP_800(prev_15_798,y_866) * x_865::node<y_866,prev_15_798>@M * 
    H_2(next_21_820,x_865) * y_866::node<next_21_820,x_865>@M
 ,
 HP_800(prev_15_798,y) ::= NONE,
 H_2(next_21_820,x) ::= NONE,
 H_3(prev_21_821,x) ::= NONE]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[]


========

[ H(x_849,y_850) ::=  y_850::node<next_19_810,prev_19_811>@M * HP_812(next_19_810,x_849) * 
HP_813(prev_19_811,x_849) * x_849::node<next_15_835,prev_15_836>@M * 
HP_789(next_15_835,y_850) * HP_0(prev_15_836,y_850)&true,

 G(x_853,y_854) ::=  
 HP_0(prev_15_788,y_854) * x_853::node<next_15_787,prev_15_788>@M * 
 G(next_15_787,y_854)&next_15_787!=null
 or HP_0(prev_15_788,y_854) * x_853::node<y_854,prev_15_788>@M * 
    HP_812(next_19_810,x_853) * y_854::node<next_19_810,x_853>@M&true
 ,
 HP_789(next_15_834,y_832) ::=  y_832::node<next_19_810,prev_19_811>@M * HP_812(next_19_810,next_15_834) * 

HP_813(prev_19_811,next_15_834) * 
next_15_834::node<next_15_830,prev_15_831>@M * HP_789(next_15_830,y_832) * 
HP_0(prev_15_831,y_832)&true,
 HP_0(prev_15_788,y) ::= NONE,
 HP_812(next_19_810,x) ::= NONE,
 HP_813(prev_19_811,x) ::= NONE]



*/
