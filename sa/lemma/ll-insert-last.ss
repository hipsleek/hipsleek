
data node {
	int val; 
	node next;	
}



HeapPred H1(node x). // non-ptrs are @NI by default
  PostPred G1(node x, node y). // non-ptrs are @NI by default
HeapPred H2(node x). // non-ptrs are @NI by default
  PostPred G2(node x, node y). // non-ptrs are @NI by default

/* HP<r> == self::node<_, null> & r=self */
/*   or self::node<_, q> * q::HP<r>; */


/* lseg<p> == self= p */
/*   or self::node<_, q> * q::lseg<p> ; */


//lemma self::HP<p1> <-> self::lseg<p1> * p1::node<_,null>;

node get_last(node x)
  infer [H1,G1]  requires  H1(x)  ensures G1(x,res);//'
                                  /*
  requires x::lseg<p> * p::node<_,null>
  ensures x::HP<p> & res=p ;//'
                                  */
{
	if (x.next == null) 
          return x;
	else {
          //x = x.next;
          return get_last(x.next);
	}
}

node insert (node x,int a)
infer [H2,G2]  requires  H2(x)  ensures G2(x,res);
/*
  requires x::lseg<p> * p::node<_,null>
  ensures res::lseg<p>* p::node<_,p1> * p1::node<_,null> ;//'
*/
{
  node last = get_last(x);
  node tmp = last.next;
  last.next = new node(a, tmp);
  //dprint;
  return x;
}
