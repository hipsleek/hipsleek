data node {
	int val; 
	node next; 
}

ll0<> == self = null
	or self::node<_, q> * q::ll0<> 
  inv true;

HeapPred H4(node a).
HeapPred H5(node a).
HeapPred H6(node b, node c).

/* function to append 2 bounded lists */
node append_bll(node x, node y)
    /* requires y::sll<m,s2,b2> & x=null  */
    /* ensures res::sll<m,s2,b2>; */
	/* requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 */
	/* ensures res::sll<nn+m, s0, b2>; */
  /* requires x::ll0<> * y::ll0<> */
  /* ensures res::ll0<>; */
  infer[H4,H5,H6]
  requires H4(x)*H5(y)
     ensures H6(y,res);
{
  node xn;
  if (x==null) return y; /* segmentation bug when returning null */
  else {
    xn = append_bll(x.next,y);
    x.next = xn;
    return x;
  }
}
