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

bool bubble(node xs)
  requires xs::node<_,p> * p::ll<>
  ensures xs::node<_,p1> * p1::ll<>;

  /* infer[H1,G1] */
  /* requires H1(xs) */
  /* ensures G1(xs); */
{
	int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
		return false;
	}
	else {
		tmp = bubble(xs.next);
    int xv = xs.val;
    int xnv = xs.next.val;
		if (xv <= xnv) 
			flag = false;
		else {
			xs.val = xnv;
			xs.next.val = xv; //ERROR: lhs and rhs do not match
			flag = true; 
		}
        //dprint;
		return (flag || tmp);
	}
}
