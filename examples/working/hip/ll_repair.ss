data node {
	node next;
}

// HeapPred P(node y).
// HeapPred Q(node y).

// node fcode(node y)
//   // infer[P,Q]
//   requires P(y)
//   ensures Q(y);

ll<n> == self = null & n = 0
	or self::node<q> * q::ll<n-1>
  inv n >= 0;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
	if (x.next == null){
        //x.next = fcode(y);
        x.next = y.next;
        }
	else {
	 	append(x.next, y);
    }
}
