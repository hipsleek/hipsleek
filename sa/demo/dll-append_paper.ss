data node{
	node next;
	node prev;
}

dll<p> == self = null or self::node<x,p> * x::dll<self>;
	
PostPred G(node a,node b).
HeapPred H(node a,node b).

void dll_append(node x, node y)
infer [H,G] requires H(x,y) ensures G(x,y);
//requires x::dll<p> * y::dll<_> & x!=null &y!=null ensures x::dll<p>;
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
  HP_799(next_15_797,y@NI) * HP_800(prev_15_798,y@NI) * HP_801(y,x@NI)&true,

 HP_799(next_15_797,y@NI) * HP_801(y,x@NI)&
  next_15_797!=null --> H(next_15_797,y)&true,

 HP_801(y,x@NI)&true --> y::node<next_21_820,prev_21_821>@M * 
  HP_822(next_21_820,x@NI) * HP_823(prev_21_821,x@NI)&true,

 HP_800(prev_15_798,y@NI) * x::node<next_15_797,prev_15_798>@M * 
  G(next_15_797,y)&next_15_797!=null --> G(x,y)&true,

 HP_800(prev_15_798,y@NI) * x::node<y,prev_15_798>@M * 
  HP_822(next_21_820,x@NI) * y::node<next_21_820,x>@M&true --> G(x,y)&true]


==================
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