data node {
  node h;
 node next;
}


lsegh<h> == self=h
  or self::node<h, q> * q::lsegh<h>
  inv true;

bool foo(node x, node h)
  requires x::lsegh<h>
  ensures  res;
 {
   if (x==h) return true;
   else {
     bool b1 = foo(x.next, h);
     bool b2 = x.h == h;
     return b1 && b2;
   }
 }
