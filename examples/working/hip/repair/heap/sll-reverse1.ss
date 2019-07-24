data node {
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<q> * q::ll<n-1>  & n > 0;

node reverse(node xs, node ys)
	requires xs::ll<n> * ys::ll<m> 
	ensures res::ll<n+m>;
{
	if (xs == null)
     return ys;
  else {
		node tmp;
		tmp = xs.next;
    // tmp = xs;
		xs.next = ys;
		return reverse(tmp, xs);
	}
}
  