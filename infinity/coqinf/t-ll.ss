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

/*return the first element of a singly linked list */
relation RF(int m, int n).
node ret_first(node x)
  infer[RF]
  requires x::ll<n> 
  ensures x::ll<m> & RF(m,n);
{
  return x;
}


/* function to insert a node in a singly linked list 
 */
relation GNN(int m, int n).
node get_next_next(node x)
  infer[n,GNN]
  requires x::ll<n> & x!=null
  ensures res::ll<m> & GNN(m,n);
{
  return x.next.next;
}

/* function to delete the node a in a singly linked list */
relation DEL2(int m, int n).
node delete2(node x, int a)
  infer[DEL2]
  requires x::ll<n>
  ensures res::ll<m> & DEL2(m,n);
{
	if (x == null)
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete2(x.next, a));
	}
}

/* function to create a singly linked list with a nodes */
relation INS(int m, int n).
void insert(node x, int a)
  infer[INS]
  requires x::ll<n> & x!=null
  ensures x::ll<m> & INS(m,n);
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

relation CL(int a, int b).
node create_list(int n, int v)
  infer[CL]
  requires true
  ensures res::ll<m> & CL(m,n);
{
  node tmp;
  if (n == 0) {
    return null;
  }
  else {
    n  = n - 1;
    tmp = create_list(n, v);
    return new node (v, tmp);
  }
}

relation TRAV(int k, int m).
void list_traverse(node x)
  infer[TRAV]
  requires x::ll<n> 
  ensures x::ll<m> & TRAV(m,n); 
{
  node t;
  if(x != null) {
    t = x;
    list_traverse(x.next);
  }
}

relation RMV(int k, int m).
void list_remove(node x, int v)
  infer[RMV]
  requires x::ll<n> & x!=null
  ensures x::ll<m> & RMV(m,n);
{
  if(x.next != null) {
    if(x.next.val == v) {
      node tmp = x.next;
      x.next = x.next.next;
      dispose(tmp);
    }
    else {
      list_remove(x.next, v);
    }
  }
}

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null; // '



relation RMV2(int k, int m).
node list_remove2(node x, int v)
  infer[RMV2]
  requires x::ll<n>
  ensures res::ll<m> & RMV2(m,n);
{
  node tmp;
  if(x != null) {
    if(x.val == v) {
      tmp = x;
      x = x.next;
      dispose(tmp);
    }
    else {
      tmp = list_remove2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}
relation CPY(int k, int m).
node list_copy(node x)
  infer[CPY]
  requires x::ll<n> 
  ensures x::ll<n> * res::ll<m> & CPY(m,n); 
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}
/*********SMALLFOOT EXAMPLES************


/*

*/
/*function to remove the first node which has value v in singly linked list*/




/*function to remove the first node which has value v in nullable singly linked list*/

*/
