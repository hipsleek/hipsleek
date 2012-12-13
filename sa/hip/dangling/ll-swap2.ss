data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a,node b).
HeapPred H3(node a).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;

void swap(ref node x, node y, node z)
  infer [H1,H2,G1,G2]
  requires H1(x)*H2(y,z)
  ensures G1(x')*G2(y,z);//'
  /*


 [ H1(x)&true --> x::node<val_82_523',next_82_524'>@L * HP_540(next_82_524')&
  true,
 HP_540(t_21')&t_21'!=null --> H1(t_21')&true,
 H2(y,z)&true --> H2(z,y)&true,
 HP_540(next_84_552)&next_84_552=null --> emp&true,
 x'::node<val_82_545,y>@M& XPURE(H2(y,z)) --> G1(x')&true,
 H2(y,z)&true --> G2(y,z)&true,
 G1(t_567) * x'::node<val_82_547,t_567>@M&true --> G1(x')&true,
 G2(z,y)&true --> G2(y,z)&true]

  */
{
    node t = x.next;
	if (t == null){
	      x.next = y;	
}
	else {
           swap(t, z, y);
              x.next=t;
}
}


