// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
tll<ll,lr,n> == self::node<null,null,lr> & self = ll & n=1
  or self::node<l,r,null> * l::tll<ll,z,n1> * r::tll<z,lr,n2> & n=n1+n2+1
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<n> == self::node<null,null,_> & n=1
	or self::node<l,r,null> * l::tree<n1> * r::tree<n2> & n=n1+n2+1
	inv self!=null;


// initializes the linked list fields
node set_right (node x, node t)
  requires x::tree<n> ensures x::tll<res,t,n>;
{
  if (x.right==null) {
    x.next = t;
    return x;
  }
  else {
    node l_most = set_right(x.right, t);
    return set_right(x.left, l_most);
  }
}

bool check_tll(node x,node t, node@R r)
  requires x::tll<t,ggg,n> ensures x::tll<t,ggg,n> & res & r'=ggg;//'
{
  if (x.right==null && x.left==null) {
    r = x.next;
    return true;
  }
  else {
    if (x.left==null || x.right==null ) return false;
    node r_most;
    bool b = check_tll(x.left, t, r_most);
    return b && check_tll(x.right, r_most, r);
  }
}

