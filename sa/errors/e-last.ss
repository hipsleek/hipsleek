data node {
  int val;
  node next;
}

ll<p> == self=p
	or self::node<_, q> * q::ll<p> & self!=null
	inv true;

HeapPred H(node a).
HeapPred G(node a, node b).

/* return the last element */
  node get_last(node x)

  infer[H,G]
  requires H(x)
  ensures G(x,res);//'

/*
case {
   x!=null ->
     requires x::node<_,next>@M * next::ll<null>
     ensures x::ll<p> * p::node<_,null>@M & res=p;
   x=null -> ensures true & flow __Error;
}
*/
/*
case {
   x!=null ->
     requires x::ll<p> * p::node<_,null>
     ensures x::ll<p> * p::node<_,null>@M & res=p;
   x=null -> ensures true & flow __Error;
}
*/
{
  if (x.next !=null)       {
    return get_last(x.next);
  }

  return x;

}

