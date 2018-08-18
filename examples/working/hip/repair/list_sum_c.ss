data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<sum> == self=null & sum = 0
	or self::node<v, r> * r::ll<sum2> & sum = v + sum2;

int sum(node x)
requires x::ll<n> ensures res = n;
{
  if (x == null) return 2;
  else {
       return x.val + sum(x.next);
  }
}

