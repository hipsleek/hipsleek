data node {
  int val;
  node next;
}

ll<n> == self=null & n=0 
  or self::node<_,q>*q::ll<n-1>
inv n>=0;

HeapPred P(node x, node y).

node zip(node x,node y)
/*
 requires x::ll<a>*y::ll<b> & a<=b
 ensures res::ll<n> & n=a;
*/
 infer[P,@classic]
 requires P(x,y)
 ensures true;
{
  if (x==null) return x;
  else {
    node r = new node(x.val+y.val,null);
    r.next = zip(x.next,y.next);
    return r;
  }
}

/*
# ex24b --ops

[ // BIND
(2;0)P(x,y)&
x!=null --> x::node<val_23_1652,next_23_1653>@M * 
            HP_1654(next_23_1653,y,x@NI)&
true,
 // BIND
(2;0)HP_1654(next_23_1653,y,x@NI)&
true |#| x::node<val_23_1652,next_23_1653>@M&
true --> y::node<val_23_1663,next_23_1664>@M * 
         HP_1665(next_23_1664,next_23_1653,x@NI,y@NI)&
true,
 // PRE_REC
(2;0)HP_1665(next_23_1664,next_23_1653,x@NI,y@NI)&
true |#| x::node<val_23_1652,next_23_1653>@M * 
         y::node<val_23_1663,next_23_1664>@M&
true --> P(next_23_1653,next_23_1664)&
true,
 // POST
(1;0)P(x,y)&y'=y & x'=x & res=x' & x'=null --> emp&
true]


*********************************************************
*******relational definition********
*********************************************************
[ P(x_1712,y_1713) ::= y_1713::node<val_23_1715,next_23_1664>@M * 
 x_1712::node<val_23_1714,next_23_1705>@M * P(next_23_1705,next_23_1664)
 or emp&x_1712=null
 (4,5)]


*/
