data node {
  node next;
}

HeapPred H(node x).
HeapPred G(node y,node@NI z).

ll<> == self=null
  or self::node<q>*q::ll<>;

void trav(ref node y)
  requires y::ll<>
  ensures y::ll<> & y'=null;
/*
{  if (y!=null) {
     y=y.next;
     trav(y);
   }
}
*/

node foo(node x)
/*
  requires x::ll<>
  ensures x::ll<> & res=null;
*/
  infer [H,G]
  requires H(x)
  ensures G(x,res);
{ 
  node y=x;
  trav(y);
  return y;
}

/*
# cyc-lseg-3.ss 


[ // PRE
(0)H(x) --> emp&
x=null,
 // POST
(0)emp&x=null & res=null & 
res=x --> G(x,res@NI)]

pre/post from auxiliary seems broken.

Obtained
--------

[ G(x_901,res_902) ::= emp&res_902=x_901 & x_901=null & res_902=null,
 H(x_900) ::= emp&x_900=null]

This answer seems to be wrong!

Expecting:
 H(x) ::= x::ll<>
 G(x,res) ::= x::ll<> & res=null

node foo(node x)
  infer [H,G]
  requires H(x)
  ensures G(x,res);
{ 
  node y=x;
  trav(y);
  return y;
}

*/