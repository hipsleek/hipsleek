
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

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;

  gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>;


bool check_ones(node x)
/*
  requires x::ll<>
  ensures x::ll<> or x::lseg<p>*p::ll<>;
*/
/*
  requires x::ll<>
  ensures x::gg<p>*p::ll<>;
*/
/*
requires x::ll<>
  ensures x::lseg<p>*p::ll<>;
*/

infer [H,G] requires H(x) ensures G(x);


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

  requires x::ll<>
  ensures x::ll<> or x::lseg<p>*p::ll<>;

Above verifies!

  requires x::ll<>
  ensures x::gg<p>*p::ll<>;

Above verifies!


The former is better since it supports better re-use of
specification and predicates.

*/

/*
*********************************************************
*******relational definition ********
*********************************************************
[ H(x_1459) ::= H(next_36_1457) * x_1459::node<val_36_1460,next_36_1457>@M
 or emp&x_1459=null
 (4,5),
 G(x_1461) ::= x_1461::node<val_36_1462,next_36_1436>@M * G(next_36_1436)
 or x_1461::node<val_36_1463,next_36_1436>@M * H(next_36_1436)
 or emp&x_1461=null
 (4,5)]

==>
 x_1461::node<val_36_1462,next_36_1436>@M * G(next_36_1436)
 or emp&x_1461=null

or

x_1461::node<val_36_1463,next_36_1436>@M * H(next_36_1436)

 */
