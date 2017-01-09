// tll with parent working example

data node4{
	node4 parent;
	node4 left;
	node4 right;
	node4 next;
}

/* predicate for a non-empty tree  */
tree<> == self::node4<_,D1,null,_>
  or self::node4<_,l,r,D2> * l::tree<> * r::tree<> & r!=null
	inv self!=null;

/* predicate for a non-empty tree with chained leaf list */

tll<p,ll,lr> == self::node4<p,D1,null,lr> & self = ll
    or self::node4<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr> & r!=null
	inv self!=null;

// initializes the linked list fields
  HeapPred H(node4 a, node4@NI p, node4@NI b).
  HeapPred G(node4 a, node4 p, node4 b, node4 c).

node4 set_right (node4 p, node4 x, node4 t)
  infer [H,G] 
  requires H(x,p,t) 
  //  ensures G(x,p,res,t) ;
       ensures G(x,res,t,p) ;
  // requires x::tree<> ensures x::tll<p,res,t>;
{
  x.parent=p;
  if (x.right==null){
    x.next = t;
    return x;
  }
  else{
    node4 l_most = set_right(x,x.right, t);
    return set_right(x,x.left, l_most);
  }
}

/*
# ex14a-tll.ss

 //  ensures G(x,p,res,t) ;
       ensures G(x,res,t,p) ;

Equiv proving Fails when parameters are permuted..

!!! INFERRED SHAPE SPEC: EBase x::tree{}<>&{FLOW,(1,28)=__flow#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume 
                   x::G{}<res,t,p>&{FLOW,(4,5)=__norm#E}[]
                   Stop Omega... 333 invocations 


*/
