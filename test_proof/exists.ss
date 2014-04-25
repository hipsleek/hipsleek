/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


/* return the first element of a singly linked list */
/*
int ret_first(node x)
	requires [nn] x::ll<nn>  & nn>1
	ensures x::ll<n>;

{
	return x.next.val;
}
*/

int foo (int x, int y)
  requires (exists r: x<r<y)
  ensures x<res<y;
{
  return x+1;
}

int main()
  requires true
  ensures true;
{
  int x = foo(1,3);
  x = foo(4,6); 
  return x;
}


