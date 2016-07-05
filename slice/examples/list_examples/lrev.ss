/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ls<p,n> == self = p & n=0
  or self::node<_, r> * r::ls<p,n-1> 
  inv n>=0 ;

coercion "lseg2" self::ls<p, n> <-> self::ls<q, n1> * q::node<_, p> & n=n1+1;

node lrev(node i, node o)
  requires i::ls<null,n>
  ensures res::ls<o,n>;
{
  if (!(i==null)) {
      // assume false;
      node k = i.next;
      i.next = o;
      return lrev(k,i);
    } else return o;
}


