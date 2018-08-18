data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<size> == self=null & size = 0
	or self::node<_, r> * r::ll<size-1>;

int size(node x)
requires x::ll<n>
ensures res = n;
{
  if (x == null) return 2;
  else {
       return 1 + size(x.next);
  }
}
