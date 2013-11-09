// simpler tll working example
data node{
  node parent;
  node left;
  node right;
}

tree<p> == self::node<p,_,null>
      or self::node<p,l,r> * l::tree<self> * r::tree<self>
	inv self!=null;

gtree<p> == self=null 
      or self::node<p,l,r> * l::gtree<self> * r::gtree<self>
	inv true;

// initializes the linked list fields

HeapPred H(node@NI p,node a).
HeapPred G(node@NI p,node a).


void trav (node p, node x)
infer [H,G] requires H(p,x) ensures G(p,x);
//requires x::tree<p>  ensures x::tree<p>;
//requires x::gtree<p>  ensures x::gtree<p>;
{
  node xp=x.parent;
  assert p=xp' assume p=xp';
  if (x.right!=null) 
    {
      // assert xl'=null;
      trav(x,x.right);
      //assert xl'!=null assume xl'!=null; //
      trav(x,x.left);
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
