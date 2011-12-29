/* singly linked lists */

/* to complete */

/* representation of a node */
data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


relation B(int x, int y).


/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
        infer [a,B]
	requires x::ll<n> & n > a //& a > 0 
	ensures x::ll<m> & B(m,n);
{
        if (a == 1)
	{
		//node tmp = x.next.next;
		//x.next = tmp;
                  x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}

