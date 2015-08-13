
data node {
 int val;
 node left;
 node right;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default


 bt<> == self=null or self::node<_,l,r>*l::bt<>*r::bt<>;

 tseg<p> == self=p
   or self::node<_,l,r>*l::bt<> * r::tseg<p>
   or self::node<_,l,r>*l::tseg<p> * r::bt<>;

  /* gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>; */


bool search(node x, int v)
/*
  requires x::bt<>
  ensures x::tseg<p>*p::bt<>;
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
