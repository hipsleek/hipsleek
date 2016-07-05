
data node {
  int val;
  node next;
}
/*
H<> == self::node<_,p> * p::ll<>
  inv true;
*/
ll<> == self=null
	or self::node<_, q> * q::ll<> & self!=null
	inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;

  /*
H1<> == self::node<_,p> & p=null
	or self::node<_, q> * q::H1<>
	inv true;
*/
HeapPred H(node a).
HeapPred G(node a, node b).

  
node foo(node x)
 infer [H,G]
 requires H(x)
     ensures  G(x, res);

/*
  requires x::H<>
  ensures x::H1<>;
*/
 {
   if (x==null) return null;
   else if (x.next == null) return x;
   else if (x.next.next ==null) return x.next;
   else return foo(x.next.next);
 }

