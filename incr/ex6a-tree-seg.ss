
data node {
 int val;
 node left;
 node right;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default

/*
sortll<n> == self=null
 or self::node<v,q>*q::sortll<v> & n<=v
 inv true; 
*/

  /* ll<> == self=null or self::node<_,q>*q::ll<>; */

  /* lseg<p> == self=p or self::node<_,q>*q::lseg<p>; */

  /* gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>; */


bool search(node x, int v)
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
  if (x==null) return false;
  else {
   int t = x.val;
   if (t==v) return true;
   else if (t<v) return search(x.left,v);
   else {
      //dprint;
     return search(x.right, v);;
   }
 }
} 
