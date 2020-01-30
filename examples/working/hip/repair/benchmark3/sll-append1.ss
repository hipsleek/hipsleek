data node {
  int val;
  node next;
}

ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2 & n > 0
  inv n >= 0;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null & n2 >= 0 & n1 > 0
  ensures exists k: x::ll<k> & k = n1 + n2 & k > 0 & n2 >= 0 & n1 > 0;
{
  if (x.next == null){
     x.next = y.next;
  } else
     append(x.next, y);
}
