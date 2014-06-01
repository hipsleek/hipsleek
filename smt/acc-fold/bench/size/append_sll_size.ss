data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or (exists v, q, m: self::node<v, q> * q::ll<m> & n = m + 1)
  inv n>=0;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 
  ensures x::ll<n1+n2>;

{
  if (x.next != null) {
    append(x.next, y);
    return;
  }
  else {
    x.next = y;
    return;
  }
}

