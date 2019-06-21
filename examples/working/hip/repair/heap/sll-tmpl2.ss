data node {
   node next;
}

ll<n> == self = null & n = 0
      or self::node<q> * q::ll<n-1>
      inv n >= 0;

HeapPred P(node x, node y, bool b).
HeapPred Q(node x, node y, bool b).


void fcode(node x, node y, bool b)
   requires P(x,y, b)
   ensures Q(x,y, b);

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
  bool b;
  fcode(x,y,b);
  if (x.next == null){
     x.next = y;
  } else append(x.next, y);
}


