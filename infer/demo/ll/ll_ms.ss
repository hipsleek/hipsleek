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



void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

void delete_list(ref node x)
  requires x::ll<n>
  ensures x'=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

//true if the container size is 0, false otherwise.
relation EMPT1(bool a).
relation EMPT2(bool a).
bool empty(node x)
  infer[EMPT1,EMPT2]
  requires x::ll<n>
  case {
  n = 0 -> ensures EMPT1(res);
  n!= 0 -> ensures EMPT2(res);
  }
{
  if (x == null) 
    return true;
  else 
    return false;
}

//The number of elements that conform the list's content.
relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[SIZEH]
  requires x::ll<m> 
  ensures SIZEH(res,m,n);
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}

relation SIZE(int a, int b).
int size(node x)
  infer[SIZE]
  requires x::ll<n>
  ensures SIZE(res,n);
{
  int m = 0;
  return size_helper(x, m);
}

//A reference to the first element in the list container.
relation FRONT(int a, int b).
int front(node x)
  infer[FRONT]
  requires x::node<v,p>*p::ll<m>
  ensures FRONT(res,v);
{
  return x.val;
}

void swap(ref node x, ref node y)
  infer @post []
  requires x::ll<n>*y::ll<m> 
  ensures x'::ll<m1>*y'::ll<n1>;
{
  node tmp = x;
  x = y;
  y = tmp;
}

//drop current content, and add n element with v value
relation ASSIGN(int a, int b, int c).
void assign(ref node x, int n, int v)
  infer[ASSIGN]
  requires x::ll<m>
  ensures x'::ll<n1> & ASSIGN(n,n1,m);
{
  x = create_list(n, v);
}

relation PUF(int a, int b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::ll<n>
  ensures x'::ll<m> & PUF(m,n);
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first element
relation PF(int a, int b).
node pop_front(ref node x)
  infer[PF]
  requires x::ll<m> & x!=null
  ensures x'::ll<n> & PF(n,m);
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two singly linked lists */
relation A(int m, int n1, int n2).
void append(node x, node y)
  infer[A]
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<m> & A(m,n1,n2);
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* return the first element of a singly linked list */
relation RF(int m, int n).
node ret_first(node x)
  infer[RF]
  requires x::ll<n> 
  ensures x::ll<m> & RF(m,n);
{
  return x;
}

/* return the tail of a singly linked list */
relation GN(int m, int n).
node get_next(node x)
  infer[GN]
  requires x::ll<n> & x!=null
  ensures x::node<_,null> * res::ll<m> & GN(m,n);
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(int m, int n).
void set_next(node x, node y)
  infer[SN]
  requires x::ll<i> * y::ll<j> & x!=null
  ensures x::ll<k> & SN(k,j);
{
  x.next = y;
}

void set_null2(ref node x)
  requires x::ll<i> & x!=null
  ensures x'::node<_,null>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::ll<i> & x!=null
  ensures x'::node<_,null>;
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(int m, int n).
node get_next_next(node x)
  infer[n,GNN]
  requires x::ll<n> & x!=null
  ensures res::ll<m> & GNN(m,n);
{
  return x.next.next;
}

/* function to insert a node in a singly linked list */
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

/* function to delete the a-th node in a singly linked list */
relation DEL(int m, int n, int p).
void delete(node x, int a)
  infer[n,a,DEL]
  requires x::ll<n>
  ensures x::ll<m> & DEL(m,n,a);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
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

/* function to reverse a singly linked list */
relation REV(node x, int k, int m, int n).
void reverse(ref node xs, ref node ys)
  infer[REV]
  requires xs::ll<n> * ys::ll<m> 
  ensures ys'::ll<k> & REV(xs',k,m,n);
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
relation SPLIT(int a, int b, int c, int d).
node split1(ref node x, int a)
  infer[SPLIT,n,a]
  requires x::ll<n>
  ensures x'::ll<n1> * res::ll<n2> & SPLIT(n,a,n1,n2);
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

/*********SMALLFOOT EXAMPLES*************/
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

/*function to remove the first node which has value v in singly linked list*/
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

/*function to remove the first node which has value v in nullable singly linked list*/
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

/*function to remove all nodes which have value v in nullable singly linked list*/
relation FIL(int k, int m).
node list_filter2(ref node x, int v)
  infer[FIL]
  requires x::ll<n>
  ensures res::ll<m> & FIL(m,n);
{
  node tmp;
  if(x != null) {
    if(x.val == v){
      tmp = x.next;
      dispose(x);
      x = tmp;
      x = list_filter2(x,v);
    }
    else{
      tmp = list_filter2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}

/**********************SLAYER (SLL) EXAMPLES***************************/
/* function to return the first node being greater than v*/
relation FGE(int k, int m).
node find_ge(node x, int v)
  infer[FGE]
  requires x::ll<n>
  ensures res = null or res::node<m,_> & FGE(m,v);
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
relation SPLICE (int a, int b, int c).
void splice (ref node x, node y)
  infer [SPLICE]
  requires x::ll<n> * y::ll<m>
  ensures x'::ll<t> & SPLICE(t,m,n); 
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
