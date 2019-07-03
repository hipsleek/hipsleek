data node {
   node next;
}

ll<n> == self = null & n = 0
      or self::node<q> * q::ll<n-1>
      inv n >= 0;

HeapPred P(node x, node y).
HeapPred Q(node x, node y).

HeapPred P1(node x, node y).
HeapPred Q1(node x, node y).

void fcode(node x, node y)
   requires P(x, y)
   ensures Q(x, y);

void fcode2(node x, node y)
   requires P1(x, y)
   ensures Q1(x, y);

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
  if (x.next == null){
     fcode2(x,y);
  }
  else fcode(x,y);
}
