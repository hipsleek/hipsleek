data node {
  node t;
 node next;
}


lsegh<t> == self=t
  or self::node<t, q> * q::lsegh<t>
  inv true;
HeapPred H(node a, node b).
HeapPred G(node a, node b).
bool foo(node x, node t)
/*
  requires x::lsegh<h>
  ensures  res;
*/
  infer [H,G]
  requires H(x,t)
     ensures  G(x,t) & res;
 {
   if (x==t) return true;
   else {
     bool b1 = foo(x.next, t);
     bool b2 = x.t == t;
     return b1 && b2;
   }
 }
