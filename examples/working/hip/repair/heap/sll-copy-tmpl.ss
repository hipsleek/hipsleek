data node {
   int val;
   node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> & n > 0;

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

node copy(node x)
requires x::ll<n>
ensures res::ll<n> * x::ll<n>;
{
  if (x == null) return x;
  else {
      node tmp;
      // tmp = copy(x.next.next);
      // tmp = copy(x.next);
      fcode(x, tmp);
      node n;
      n = new node(x.val, tmp);
      return n;
  }
}
