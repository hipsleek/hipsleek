/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<n> == self = null & n=0
	or self::node<v, r> * r::ll<n-1> 
  inv n>=0;

ll2<i,j> == self = null & i=j
  or self::node<v, r> * r::ll2<i+1,j> 
  inv i<=j;

/*
relation zeros(int[] a, int i, int j) == (i > j 
     | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] = 0))).
*/

/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<m> * y::ll<n> & x!=null
  ensures x::ll<m+n>;

{
	if (x.next == null) {
          //assume false;
		x.next = y;
	} else {
		//assume false;
		append(x.next, y);
	}
}

