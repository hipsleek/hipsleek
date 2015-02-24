// simpler tll working example

data node{
  node left;
  node right;
}


tree<> == self::node<_,null>
        or self::node<l,r> * l::tree<> * r::tree<>
	inv self!=null;

// initializes the linked list fields

HeapPred H(node a).
HeapPred G(node a).


void trav (node x)
infer [H,G] requires H(x) ensures G(x);
//requires x::tree<>  ensures x::tree<>;
{
  node xl = x.left;
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
# tree-1.ss -gen-sa-sleek-file

Why did we have /&\?

[ H(x) ::= x::node<left,right>@M * (DP_961(left)/&\H(left))&right=null,

 G(x) ::= x::node<left,right>@M * H(left)&right=null
 or x::node<left,right>@M * DP_961(left)&right=null
 or x::node<left,right>@M * G(left) * G(right)&right!=null
 ,
 DP_961(left) ::= NONE]

sleek file has more stuff...

[ DP_41(left) ::= NONE,

 G(x) ::= x::node<left,right>@M * H(left)&right=null
 or x::node<left,right>@M * DP_41(left)&right=null
 or x::node<left,right>@M * G(left) * G(right)&right!=null,
 H(x) ::= x::node<left,right>@M * (DP_41(left)/&\H(left))&right=null,
 HP_914(left1) |#| x::node<left_24_42,right_24_913>@M&
  right_24_913=null ::= DP_41(left) or H(left1),
 HP_915(right) ::=  H(right)&right!=null or emp&right=null
 ]

relational assumptions..

[ // BIND
(0)H(x) --> x::node<left,right>@M * HP_914(left) * HP_915(right),
 // PRE_REC
(1;0)HP_915(right)&right!=null --> H(right),
 // PRE_REC
(1;0)HP_914(left) --> H(left),
 // POST
(1;0)x::node<left,right>@M * G(left) * G(right)&right!=null --> G(x),
 // POST
(2;0)x::node<left,right>@M * HP_914(left) * HP_915(right)&right=null --> G(x)]

// sleek file
relAssume 
 (0)H(x) --> x::node<left_24_912,right_24_913>@M * HP_914(left_24_912) * 
  HP_915(right_24_913).
relAssume 
 (1;0)HP_915(right_24_913)&right_24_913!=null --> H(right_24_913).
relAssume 
 (1;0)HP_914(left_24_912) --> H(left_24_912).
relAssume 
 (1;0)x::node<left_24_912,right_24_913>@M * G(right_24_913) * G(left_24_912)&
  right_24_913!=null --> G(x).
relAssume 
 (2;0)HP_914(left_24_912) * HP_915(right_24_913) * 
  x::node<left_24_912,right_24_913>@M&right_24_913=null --> G(x).


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
