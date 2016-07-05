// TODO: Problem with renaming variables.

/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1 & S=union(S1, {v})
  inv n>=0;


// drop current content, and add n element with v value
void assign(ref node x, int n, int v)
  infer @post []
  requires x::ll2<m,S>
  ensures x'::ll2<n,S1> ; //
{
  x = create_list(n, v);
}

relation CL(bag a, int b).
node create_list(int n, int v)
  infer[CL]
  requires n>=0
  case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::ll2<n,S> & CL(S,v);// forall _x: _x notin S | _x = v;
  n < 0 -> ensures true;
  }
{
  node tmp;
  if (n == 0) {
    return null;
  }
  else {
    n = n - 1;
    tmp = create_list(n,v);
    return new node (v, tmp);
  }
}
