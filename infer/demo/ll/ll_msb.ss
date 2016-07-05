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

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

void delete_list(ref node x)
  requires x::ll2<n,S>
  ensures x'=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

bool empty(node x)
  requires x::ll2<n,S>
  ensures true;
{
  if (x == null) return true;
  else return false;
}

//The number of elements that conform the list's content.
int size_helper(node x, ref int n)
  requires x::ll2<m,S> & 0<=m
  ensures res=m+n & m>=0;
{
  if (x==null) return n;
  else {
    n = n + 1;
    return size_helper(x.next, n);
  }
}

int size(node x)
  requires x::ll2<n,_> & 0<=n
  ensures res=n;
{
  int m = 0;
  return size_helper(x, m);
}

//A reference to the first element in the list container.
int front(node x)
  requires x::node<v,p>*p::ll2<m,_>
  ensures res=v;
{
  return x.val;
}

relation SWAP(bag a, bag b, bag c, bag d).
void swap(ref node x, ref node y)
  infer [SWAP]
  requires x::ll2<n,S1>*y::ll2<m,S2>
  ensures x'::ll2<m,S3>*y'::ll2<n,S4> & SWAP(a,b,c,d);
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
relation ASSIGN(int a, bag b).
void assign(ref node x, int n, int v)
  infer [ASSIGN]
  requires x::ll2<m,S3> & n>=0
  case {
  n = 0 -> ensures x'=null;
  n > 0 -> ensures x'::ll2<n,S4> & ASSIGN(a,S4);
  n < 0 -> ensures true;
  }
{
  x = create_list1(n, v);
}

relation PUF(bag a, bag b, int b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::ll2<n,S>
  ensures x'::ll2<n+1,S1> & PUF(S1,S,v);
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first element
relation PF(bag a, bag b).
node pop_front(ref node x)
  infer[PF]
  requires x::ll2<m,S1> & x!=null
  ensures x'::ll2<m-1,S2> & PF(S1,S2); 
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two singly linked lists */
relation APP(bag a, bag b, bag c).
void append(node x, node y)
  infer [APP]
  requires x::ll2<n1,S1> * y::ll2<n2,S2> & x!=null
  ensures x::ll2<m,S> & m=n1+n2 & APP(S,S1,S2); 
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* return the first element of a singly linked list */

relation RETF(bag a, bag b).
node ret_first(node x)
  infer [RETF]
  requires x::ll2<n,S1>
  ensures x::ll2<n,S2> & RETF(S1,S2); 
{
  return x;
}

/* return the tail of a singly linked list */
relation GN(bag a, bag b, bag c).
node get_next(ref node x)
  infer[GN]
  requires x::ll2<n,S> & x!=null
  ensures x'::ll2<1,S1> * res::ll2<n-1,S2> & GN(S,S1,S2);
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(bag a, bag b, int c).
void set_next(ref node x, node y)
  infer[SN]
  requires x::node<v,t>*t::ll2<_,_>*y::ll2<j,S>& x!=null
  ensures x::ll2<k,S2> & k>=1 & k=j+1 & SN(S,S2,v);
{
	x.next = y;
}

void set_null2(ref node x)
  requires x::ll2<i,_> & x!=null
  ensures x'::ll2<1,_>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::ll2<i,S> & x!=null
  ensures x'::node<_,null>;
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(bag a, bag b).
node get_next_next(node x)
  infer[GNN]
  requires x::ll2<n,S> & n > 1
  ensures res::ll2<n-2,S2> & GNN(S,S2); 
{
  return x.next.next;
}

/* function to insert a node in a singly linked list */
relation INS(bag a, bag b, int a).
void insert(node x, int a)
  infer [INS]
  requires x::ll2<n,S> & n > 0
  ensures x::ll2<n+1,S1> & INS(S,S1,a);
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

/* function to delete the a-th node in a singly linked list */
relation DEL(bag a, bag b).
void delete( node x, int a)
  infer [DEL]
  requires x::ll2<n,S> & n > a & a > 0
  ensures x::ll2<m,S1> & DEL(S,S1);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the node a in a singly linked list */
relation DEL2(int a, bag b, bag c).
node delete2(node x, int a)
  infer [DEL2]
  requires x::ll2<n,S>
  ensures res::ll2<m,S1> & m<=n & DEL2(a,S,S1);
{
	if (x == null)
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete2(x.next, a));
	}
}

/* function to create a singly linked list with a nodes */
node create_list1(int n, int v)
  requires n>=0
 case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::ll2<n,S> & (forall (x: x notin S | x = v));
  n < 0 -> ensures true;
}

relation CL(bag a, int b).
node create_list(int n, int v)
  infer[CL]
  requires n>=0
  case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::ll2<n,S> & CL(S,v);
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

/* function to reverse a singly linked list */
relation REV(bag a, bag b, bag c).
void reverse(ref node xs, ref node ys)
  infer [REV]
  requires xs::ll2<n,S1> * ys::ll2<m,S2>
  ensures ys'::ll2<n+m,S> & xs' = null & REV(S,S1,S2); 
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
relation SPLIT(bag a, bag b, bag c).
node split1(ref node x, int a)
  infer[SPLIT]
  requires x::ll2<n, S> & a > 0 & n > a
  ensures x'::ll2<n1, S1>*res::ll2<n2, S2> & n=n1+n2 & n1>0 & n2>0 & n1=a & SPLIT(S,S1,S2);
{
	node tmp;

	if (a == 1)
	{
		tmp = x.next; 
		x.next = null;
		return tmp;
	}
	else
	{
		a = a - 1;
		node tmp;
		bind x to (_, xnext) in {
			tmp = split1(xnext, a);
		}
		return tmp;
	}
}

/*****************************************/
/*********SMALLFOOT EXAMPLES*************/
relation TRAV(bag a, bag b).
void list_traverse(node x)
  infer [TRAV]
  requires x::ll2<n,S1>
  ensures x::ll2<n,S2> & TRAV(S1,S2);
{
  node t;
  if(x != null) {
    t = x;
    list_traverse(x.next);
  }
}

relation CPY(bag a, bag b).
node list_copy(node x)
  infer [CPY]
  requires x::ll2<n,S>
  ensures x::ll2<n,S> * res::ll2<n,S2> & CPY(S,S2); 
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

/*function to remove the first node which has value v in singly linked list*/
void list_remove(node x, int v)
  requires x::ll2<n,S> & n > 0
  ensures x::ll2<m,S2> & m <= n;
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

/*function to remove the first node which has value v in nullable singly linked list*/
relation RMV2(bag a, bag b).
node list_remove2(node x, int v)
  infer[RMV2]
  requires x::ll2<n,S> & n >= 0
  ensures res::ll2<m,S2> & m <= n & RMV2(S,S2);
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

/*function to remove all nodes which have value v in nullable singly linked list*/
relation FIL(bag a, bag b).
node list_filter2(node x, int v)
  infer [FIL]
  requires x::ll2<n,S> & n >= 0
  ensures res::ll2<m,S2> & m <= n & FIL(S,S2);
{
  node tmp;
  if(x != null) {
    if(x.val == v){
      tmp = x.next;
      dispose(x);
      x = tmp;
      x = list_filter2(x,v);
    }
    else
    {
      tmp = list_filter2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}

/**************************************************************/
/**********************SLAYER (SLL) EXAMPLES***************************/

/* function to return the first node being greater than v*/
relation FGE(bag a, int b).
node find_ge(node x, int v)
  infer[FGE]
  requires x::ll2<n,S> & n >= 0
  ensures res = null or res::node<m,_> & m > v & FGE(S,m);
{
  if(x == null)
    return null;
  else {
    if(x.val > v)
      return x;
    else
      return find_ge(x.next, v);
  }
}

/*function to splice 2 linked list*/
relation SPI(bag S1, bag S2, bag S3).
void splice (ref node x, node y)
  infer[SPI]
  requires x::ll2<n,S1> * y::ll2<m,S2>
  ensures x'::ll2<m+n,S> & SPI(S,S1,S2);
{
  if(x == null)
    x = y;
  else {
    if(y != null){
      node nx = x.next;
      node ny = y.next;
      x.next = y;
      splice(nx, ny);
      y.next = nx;
    }
  }
}
