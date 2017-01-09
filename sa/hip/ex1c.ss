data node {
  int val;
  node next;
}

ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;


HeapPred H5(node a).
HeapPred G1(node a, node b).

node foo3(node@R x)
 infer [H5,G1]
 requires H5(x)
 ensures  G1(x',res); //'
 {
   node tmp;
   tmp = get_next1(x);
   return tmp;
 }

HeapPred H6(node a).
HeapPred G2(node a, node b).

node get_next(node@R x)
  infer[H6,G2]
  requires H6(x)
  ensures G2(x',res);//'
{
  node t = x.next;
  x.next = null;
  return t;
}

node get_next1(node@R x)
  requires x::node<_,p>
  ensures x'::node<_,null> & res=p;//'
{
  node t = x.next;
  x.next = null;
  return t;
}
