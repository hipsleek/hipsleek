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

/*

Inferred Pure:[ n!=0 | a!=1, n!=0 | a!=1, n!=1 | a!=1, (n!=0 | 2>a) & (n!=0 | a>0)]
& (n!=0 | 2>a) & 
       (n!=0 | a>0) 
 */

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
    infer  [a,n]
    requires x::ll<n> //& (n!=0 | 2>a) & (n!=0 | a>0)
	ensures x::ll<m> & n>=2 & n=m+1;
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

