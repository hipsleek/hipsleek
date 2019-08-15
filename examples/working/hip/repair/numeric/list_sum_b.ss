func int tf(int k) == ?.

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
  if (x == null) return 0;
  else {
       int k;
       k = sum(x.next);
       return x.val - tf(k);
  }
}

