data node {
   node next;
}

ll<n> == self = null & n = 0
      or self::node<q> * q::ll<n-1>
      inv n >= 0;

// HeapPred P(node x, node y).
// HeapPred Q(node x, node y).


// bool fcode(node x, node y)
//    requires P(x,y)
//    ensures Q(x,y);

HeapPred P(node x).
HeapPred Q(node x).

bool fcode(node x)
   requires P(x)
   ensures Q(x);

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
  // if (x.next == null){
  if (fcode(x)){
     // fcode(x,y);
     x.next = y;
  }
}


// void append(node x, node y)
//   requires x::ll<n1> * y::ll<n2> & x!=null
//   ensures x::ll<n1+n2>;
// {
//   if (fcode(x)){
//      x.next = y;
//   } else append(x.next, y);
// }
