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


/*
relation zeros(int[] a, int i, int j) == (i > j 
     | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] = 0))).
*/

ll2<i,j,a> == self = null & i=j
  or self::node<v, r> * r::ll2<i+1,j,a> & a[i]=v 
  inv i<=j;

/* append two singly linked lists */
void append(node x, node y)
  requires x::ll2<i,j,a> * y::ll2<j,k,a> & i<j //& x!=null
  ensures x::ll2<i,k,a>;
{
	if (x.next == null) {
		x.next = y;
	} else {
		append(x.next, y);
	}
}

/*
# ll-b.ss -tp z3

ll2<i,j,a> == self = null & i=j
  or self::node<v, r> * r::ll2<i+1,j,a> & a[i]=v 
  inv i<=j;

Why is Omega still called?

Omega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a_1041[i_1094]")
 Formula: exists(i_1094:i_1038=1+i_1094 & v_1097=a_1041[i_1094])

*/
