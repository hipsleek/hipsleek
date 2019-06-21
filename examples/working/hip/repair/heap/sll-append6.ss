data node {
	node next;
}

ll<n> == self = null & n = 0
	or self::node<q> * q::ll<n-1> & n > 0;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
	if (x.next == null){
       x.next = y;
   } else {
       // append(x.next, y.next);
       append(x,y.next);
    }
}