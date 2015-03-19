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

relation dom1(int[] a, int low, int high).

axiom dom1(a,low,high) & low<=l & h<=high ==> dom1(a,l,h).
axiom l>=h ==> dom1(a,l,h).
axiom dom1(a,l,k) & dom1(a,k,h) ==> dom1(a,l,h).

/*
relation zeros(int[] a, int i, int j) == (i > j 
     | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] = 0))).
*/

ll2<i,j,a> == self = null & i=j
  or self::node<v, r> * r::ll2<i+1,j,a> & a[i]=v & dom1(a,i,i+1) 
  inv i<=j & dom1(a,i,j);

/* append two singly linked lists */
void inc(node x)
/*
  requires x::ll<n> 
  ensures x::ll<n>;
*/
requires x::ll2<i,j,a>
ensures x::ll2<i,j,b>;// & forall(k: i <= k & k <= j & b[k] = a[k] + 1);

{
        
	if (x == null) {//assume false;
	//dprint;
		return;
	} else {
                x.val = x.val+1;
		inc(x.next);
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
