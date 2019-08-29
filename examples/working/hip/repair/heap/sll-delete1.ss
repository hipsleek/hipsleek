data node {
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<q> * q::ll<n-1> & n > 0;

void delete(node x, int a)
	requires x::ll<n> & n > a & a > 0 
	ensures x::ll<n - 1>;
{
  if (a == 1)
	{
    x.next = x.next.next;
	}
	else {
		delete(x.next, a - 2);
	}	
}
