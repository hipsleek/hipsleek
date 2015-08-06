
data node {
 int val;
 node next;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default

/*
sortll<n> == self=null
 or self::node<v,q>*q::sortll<v> & n<=v
 inv true; 
*/

bool check_ones(node x)
  infer [H,G]
  requires H(x)
  ensures G(x);
//requires x::sortll<v>@L ensures  res;
{ 
  if (x==null) return true;
  else {
   int t = x.val;
   if (t==1) return check_ones(x.next);
   else {
      //dprint;
       return false;
   }
 }
} 

/*
# check-ones.ss 

Given:

  infer [H,G]
  requires H(x)
  ensures G(x);

Obtained:

[ H(x_1414) ::= H(next_24_1412) * x_1414::node<val_24_1415,next_24_1412>@M
 or emp&x_1414=null
 (4,5),
 G(x_1416) ::= x_1416::node<val_24_1417,next_24_1391>@M * G(next_24_1391)
 or x_1416::node<val_24_1418,next_24_1391>@M * H(next_24_1391)
 or emp&x_1416=null
 (4,5)]

Do we need to refactor G ?

  H<> == self::ll<>
  G<p> == self=null or self=p or self::node<_,q>*q::G<p>
 
  requires x::ll<>
  ensures  x::G<p> * p::ll<>

This can be further re-factored as:

  H<> == self::ll<>
  G<p> == self::ll<> or self::lseg<p>*p::ll<>;

  in order to reuse x::ll<> and x::lseg<p>


*/
