data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>;

node copy(node x)
requires x::ll<n>
ensures res::ll<n> * x::ll<n>;
{
  if (x == null) return x.next;
  else {
      node tmp = copy(x.next);
      node n = new node(x.val, tmp);
      return n;
  }
}

