data node {
  node next;
  node down;
}

HeapPred H(node x).
HeapPred G(node y, node@NI z).

ll<> == self=null
  or self::node<_,q>*q::ll<>;

lll<> == self=null
  or self::node<n,q>*n::lll<>*q::ll<>;

void trav(ref node z)
  requires z::ll<>
  ensures z::ll<> & z'=null;
{  if (z!=null) {
     z=z.down;
     trav(z);
   }
}

void outer(ref node x)
  infer [H,G]
  requires H(x)
  ensures G(x,x');
/*
  requires x::lll<>
  ensures x::lll<> & x'=null;
*/
{  if (x!=null) {
     node z=x.down;
     trav(z);
     x=x.next;
     outer(x);
   }
}


/*
# cyc-lseg-4.ss 

minor issue with  x_942=0

Obtained
--------
[ G(x_943,x_944) ::= 
 x_943::node<next_33_916,down_33_917>@M * down_33_917::ll@M * 
 G(next_33_916,x_944)
 or emp&x_943=x_944 & x_944=null & x_943=null
 ,
 H(x_942) ::= 
 H(next_33_939) * down_33_938::ll@M * x_942::node<next_33_939,down_33_938>@M
 or emp&x_942=0
 ]

This answer looks good but x_942=0 should have been converted
to null by our ptr conversion.

*/
