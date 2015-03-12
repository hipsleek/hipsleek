data node {
  int val;
  node next;
}

/* ll<n> == self = null & n=0 */
/* 	or self::node<_, q>* q::ll<n-1>  */
/*   inv true; */

ll<> == self = null  
  or self::node<_, q>* q::ll<>;

 HeapPred U(node a).

llu<> == U(self)  
  or self::node<_, q>* q::llu<>;

  lly<> == self::node<_, q>* q::lly<>;

 HeapPred H1(node a).
HeapPred H2(node a).
      HeapPred H(node a, node@NI b).
// HeapPred G1(node a, node b, node c).
      HeapPred G1(node a, node b).


  void reverse(ref node x, ref node y)
      infer [H,G1]
      requires H(x,y)
     ensures G1(x',y');//'

/*
  requires x::ll<> * y::llu<>
  ensures y'::llu<>;//'

  requires x::ll<> * y::ll<>
  ensures y'::ll<>;//'

   infer [H1,G1]
    requires H1(x,y)
     ensures G1(x');

*/
{
  if(x!= null){
    node tmp = x.next;
    x.next = y;
    y = x;
    x = tmp;
    //dprint;
    reverse(x,y);
    // dprint;
  }
  // else x=y;
}
