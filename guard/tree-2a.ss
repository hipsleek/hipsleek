// simpler tll working example
data node{
  node left;
  node right;
}

tree<> == self::node<_,null>
      or self::node<l,r> * l::tree<> * r::tree<>
	inv self!=null;

gtree<> == self=null 
      or self::node<l,r> * l::gtree<> * r::gtree<>
	inv true;

// initializes the linked list fields

void trav (node x)
//infer [H,G] requires H(p,x) ensures G(p,x);
//requires x::tree<p>  ensures x::tree<p>;
requires x::gtree<>  ensures x::gtree<>;
{
  if (x.right!=null) 
    {
      // assert xl'=null;
      trav(x.right);
      //assert xl'!=null assume xl'!=null; //
      trav(x.left);
    }
  else {
    ;
    //assert xl'=null assume xl'=null; //
  }
}

/*
# tree-1.ss

GOT
===
[ G(x_951) ::= 
 x_951::node<left_24_912,right_24_913>@M * G(right_24_913) * G(left_24_912)&
 right_24_913!=null
 or x_951::node<left_24_912,right_24_913>@M * H(left_24_912)&
    right_24_913=null
 ,
 H(x_949) ::= H(left_24_943) * x_949::node<left_24_943,right_24_944>@M 
    * HP_915(right_24_944),
 HP_915(right_24_950) ::= emp&right_24_950=null
 or H(left_24_946) * right_24_950::node<left_24_946,right_24_947>@M * 
    HP_915(right_24_947)
 ]

EXPECTING
=========
tree<> == self::node<_,null>
        or self::node<l,r> * l::tree<> * r::tree<>
	inv self!=null;

=======================================

HeapPred H(node a).
HeapPred H0(node lf8).
HeapPred H1(node r9).
HeapPred G(node a).

H(x) --> x::node<lf8,r9>@M * H0(lf8) * H1(r9).

H1(r9)& r9!=null --> H(r9).

H0(lf8)  --> H(lf8) .

x::node<lf8,r9>@M * G(r9) * G(lf8)&r9!=null --> G(x).

H0(lf8) * H1(r9) * x::node<lf8,r9> &r9=null --> G(x).

//H0(lf8) --> true
H1(r9) & r9!=null --> H(r9).
H1(r9) & r9=null --> true

H0(lf8) |#| x::node<r9,lf8>& r9!=null --> H(lf8) .

H0(lf8) |#| x::node<r9,lf8>& r9=null --> true .

H0(lf8) --> H(lf8) |#| x::node<r9,lf8>& r9!=null 
            or emp |#| x::node<r9,lf8>& r9=null 

H1(r9) --> H(r9) & r9!=null or r9=null.


H(x) --> x::node<lf8,r9>@M * H0(lf8) * H1(r9).
   --> x::node<lf8,r9>@M * H0(lf8) * (H(r9) & r9!=null or r9=null).
   -->  x::node<lf8,r9>@M * H0(lf8) * H(r9) & r9!=null
       or  x::node<lf8,null>@M * H0(lf8) .
   -->  x::node<lf8,r9>@M * H(lf8) * H(r9) & r9!=null
       or  x::node<lf8,null>@M .



*/
