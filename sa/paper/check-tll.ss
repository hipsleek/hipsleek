// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,_> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a, node@NI b, node@NI c).
HeapPred G(node a, node@NI b, node@NI c).

bool check_tll(node x,node t, node@R r)
  infer [H,G] requires H(x,t,r) ensures G(x,t,r) & res;//'
//  requires x::tll<t,ggg>@L ensures res & r'=ggg;//'
{
  if (x.right==null && x.left==null)
    {
      r = x.next;
      return true;
    }
  else
    {
      if (x.left==null || x.right==null ) return false;
      node r_most;
      bool b = check_tll(x.left, t, r_most);
      return b && check_tll(x.right, r_most, r);
    }
}

/*
# check-tll.ss --sa-dnc --pred-en-dangling

*/
