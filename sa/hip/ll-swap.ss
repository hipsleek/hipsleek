data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a).
HeapPred G2(node a).
HeapPred G3(node a).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;

void swap(ref node x, node y, node z)
  infer [H1,H2,H3,G1,G2,G3]
  requires H1(x)*H2(y)*H3(z)
  ensures G1(x')*G2(y)*G3(z);//'
  /*

 H1(x)&true --> x::node<val_25_521',next_25_522'> * HP_538(next_25_522')&true,
 HP_538(t_21')&t_21'!=null --> H1(t_21')&true,
 H2(y) * H3(z)&true --> H2(z) * H3(y)&true,
 H2(y)&true --> H3(y)&true,
 HP_538(next_27_550)&next_27_550=null --> emp&true,
 x'::node<val_25_543,y>&H2_y_564=y --> G1(x')&true,
 H2(y)&H2_y_564=y --> G2(y)&true,
 H3(z)&true --> G3(z)&true,
 G1(t_566) * x'::node<val_25_545,t_566>&true --> G1(x')&true,
 G2(z) * G3(y)&true --> G2(y) * G3(z)&true,
 G2(z)&true --> G3(z)&true]

Why not decompose these further?

 H2(y) * H3(z)&true --> H2(z) * H3(y)&true,
 G2(z) * G3(y)&true --> G2(y) * G3(z)&true,
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


