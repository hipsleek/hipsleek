data node {
  int val;
	node next;
}

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
	if (x.next == null){
       x.next = y.next;
       // x.next = y;
   } else {
       append(x.next, y);
    }

}