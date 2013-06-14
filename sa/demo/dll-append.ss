data node{
	node next;
	node prev;
}

dll<p> == self = null or self::node<x,p> * x::dll<self>;

dllt<p,tl> == self = tl	or self::node<x,p> * x::dllt <self,tl>;
	
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G(node a).
HeapPred G3(node a,node b).
HeapPred H3(node a,node b).

void dll_append(node l1, node l2)
// infer [H1,H2,G] requires H1(l1)*H2(l2) ensures G(l1);
infer [H3,G3] requires H3(l1,l2) ensures G3(l1,l2);
//requires l1::dll<p> * l2::dll<_> & l1!=null  ensures l1::dll<p>;
// requires l1::dllt<p,null> * l2::dll<_> & l1!=null  ensures l1::dll<p>;


{
	if (l1.next!=null)
		dll_append(l1.next,l2);
	else 
		{
			l1.next = l2;
			if (l2!=null) l2.prev = l1;
		}
}

/*
 id: 21; caller: []; line: 51; classic: false; kind: BIND; hec_num: 5; evars: []; infer_vars: [H3,G3,HP_817,HP_818]; c_heap: emp
 checkentail (HP_817(next_46_815,l2)) * (HP_818(prev_46_816,l2)) * 
l1'::node<l2',prev_46_816>@M[Orig]&l1=l1' & l2=l2' & next_46_815=null & 
!(v_bool_46_796') & next_46_815=null & !(v_bool_46_796') & 
next_46_815=next_50_834 & l2'!=null & v_bool_51_795' & l2'!=null & 
v_bool_51_795'&{FLOW,(22,23)=__norm}[]
 |-  l2'::node<next_51_793',prev_51_794'>@M[Orig]&true&{FLOW,(1,25)=__flow}[]. 
hprel_ass: [ (HP_817(next_46_815,l2)) * (HP_818(prev_46_816,l2))&l2!=null & 
  next_46_815=null --> (HP_843(next_51_841,next_46_815)) * 
  (HP_844(prev_51_842,next_46_815))&true]
res:  [
  l1'::node<l2',prev_46_816>@M[Orig] * (HP_843(next_51_841,next_46_815)) * (HP_844(prev_51_842,next_46_815))&l1=l1' & l2=l2' & next_46_815=null & !(v_bool_46_796') & next_46_815=null & !(v_bool_46_796') & next_46_815=next_50_834 & l2'!=null & v_bool_51_795' & l2'!=null & v_bool_51_795' & next_51_793'=next_51_841 & prev_51_794'=prev_51_842&{FLOW,(22,23)=__norm}[]
  ]


[ 

 H3(l1,l2)&true --> l1::node<next_22_815,prev_22_816>@M * 
 HP_7(next_22_815,l2) * HP_8(prev_22_816,l2).

 HP_7(next_22_815,l2)&next_22_815!=null --> H3(next_22_815,l2)&true.

 HP_7(next_22_815,l2) * HP_8(prev_22_816,l2) & l2!=null & 
  next_22_815=null --> HP_843(next_27_841,next_22_815) * 
  HP_844(prev_27_842,next_22_815).

 HP_8(prev_22_816,l2) * l1::node<next_22_815,prev_22_816>@M * 
  G3(next_22_815,l2)&next_22_815!=null --> G3(l1,l2)&true,

 l1::node<l2,prev_22_816>@M * HP_843(next_27_841,next_22_815) * 
  HP_844(prev_27_842,next_22_815) * l2::node<next_27_841,l1>@M&
  next_22_815=null --> G3(l1,l2)&true,

 HP_7(next_22_815,l2) * HP_8(prev_22_816,l2) * 
  l1::node<l2,prev_22_816>@M&next_22_815=null & l2=null --> G3(l1,l2)&true]
*/

