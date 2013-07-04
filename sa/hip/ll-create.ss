data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null
	or self::node<_, q> * q::ll<>
  inv true;

HeapPred H1(node a).
HeapPred G1(node a).
node create_list(int a)
	/* requires a >= 0  */
	/* ensures res::ll<>; */
  infer[G1]
  requires true
  ensures G1(res);
{
  node tmp;

	if (a == 0) {
      // assume false;
		return null;
	}
	else {
		a  = a - 1;
        //    dprint;
		tmp = create_list(a);
        //    dprint;
		return new node (0, tmp);
	}
}
