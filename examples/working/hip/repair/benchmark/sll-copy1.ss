data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> & n > 0;

node copy(node x)
requires x::ll<n>
ensures res::ll<n> * x::ll<n>;
{
  if (x == null) return x;
  else {
      node tmp;
      tmp = copy(x.next.next);
      // tmp = copy(x.next);
      node n;
      n = new node(x.val, tmp);
      return n;
  }
}

