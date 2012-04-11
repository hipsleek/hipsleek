/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll1<> == self = null
	or self::node<_, q> * q::ll1<>
  inv true;


void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

relation A (node x).
void delete_list(ref node x)
  infer [A]
  requires x::ll1<>
  ensures A(x'); 
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
  requires x::ll1<>
  case {
    x = null -> ensures EMPT1(res);
    x != null -> ensures EMPT2(res);
  }
{
  if (x == null)
    return true;
  else
    return false;
}

//The number of elements that conform the list's content.
int size_helper(node x, ref int n)
  requires x::ll1<>
  ensures true;
{
  if (x==null)
    return n;
  else
  {
    n = n+1;
    return size_helper(x.next, n);
  }
}

int size(node x)
  requires x::ll1<>
  ensures true;
{
  int n = 0;
  return size_helper(x, n);
}

// A reference to the first element in the list container.
int front(node x)
  infer [x]
  requires x::ll1<> 
  ensures true;
{
  return x.val;
}

void swap(ref node x, ref node y)
  requires x::ll1<>*y::ll1<>
  ensures x'::ll1<>*y'::ll1<>;
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
void assign(ref node x, int n, int v)
  requires x::ll1<>
  ensures true;
{
  x = create_list(n, v);
}

void push_front(ref node x, int v)
  requires x::ll1<>
  ensures x'::node<v,p>*p::ll1<>;
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first element
node pop_front(ref node x)
  infer[x]
  requires x::ll1<>
  ensures x'::ll1<>;
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two singly linked lists */
void append(node x, node y)
  infer[x]
  requires x::ll1<> * y::ll1<> 
  ensures x::ll1<>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)
  requires x::ll1<>
  ensures x::ll1<>;
{
  return x;
}

/* return the tail of a singly linked list */
node get_next(node x)
  infer[x]
  requires x::ll1<> 
  ensures true;
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
void set_next(node x, node y)
  infer[x]
  requires x::ll1<> * y::ll1<> 
  ensures x::ll1<>;
{
	x.next = y;
}

void set_null2(node x)
  infer[x]
  requires x::ll1<> 
  ensures x::node<_,r>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(node x)
  infer[x]
  requires x::ll1<>
  ensures x::node<_,r>;
{
  x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x)
  infer[x]
  requires x::ll1<>
  ensures res::ll1<>;
{
  if (x.next!=null)
    return x.next.next;
  else 
    return null;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
  infer[x]
  requires x::ll1<>
  ensures x::ll1<>;
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
  infer[x]
  requires x::ll1<> & a > 0
  ensures x::ll1<>;
{
  if (a == 1)
    {
      x.next = x.next.next;
    }
  else
    {
      delete(x.next, a-1);
    }
}

/* function to delete the node a in a singly linked list */
node delete2(node x, int a)
  requires x::ll1<>
  ensures res::ll1<>;
{
	if (x == null)
		return x;
	else
  {
		if (x.val == a)
      return x.next;
		else
      return new node(x.val, delete2(x.next, a));
  }
}

/* function to create a singly linked list with a nodes */
node create_list(int n, int v)
  requires true 
  ensures res::ll1<>;
{
  node tmp;
  if (n == 0)
  {
    return null;
  }
  else
  {
    n  = n - 1;
    tmp = create_list(n, v);
    return new node (v, tmp);
  }
}

/* function to reverse a singly linked list */
relation REVERSE(node x).
void reverse(ref node xs, ref node ys)
  infer [REVERSE]
  requires xs::ll1<> * ys::ll1<>
  ensures ys'::ll1<> & REVERSE(xs');
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
node split1(node x, int a)
  infer[x]
  requires x::ll1<> & a > 0 
  ensures x::ll1<> * res::ll1<>;
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
		bind x to (_, xnext) in
        {
          tmp = split1(xnext, a);
		}
		return tmp;
	}
}

/*****************************************/
/*********SMALLFOOT EXAMPLES*************/
void list_traverse(node x)
  requires x::ll1<>
  ensures x::ll1<>;
{
  node t;
  if(x != null) {
    t = x;
    list_traverse(x.next);
  }
}

node list_copy(node x)
  requires x::ll1<>
  ensures x::ll1<> * res::ll1<>;
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
  infer[x]
  requires x::ll1<> 
  ensures x::ll1<>;
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
node list_remove2(node x, int v)
  requires x::ll1<>
  ensures res::ll1<> ;
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
node list_filter2(node x, int v)
  requires x::ll1<>
  ensures res::ll1<>;
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
node find_ge(node x, int v)
  requires x::ll1<>
  ensures res = null or res::node<m,_> & m > v;
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
void splice (ref node x, node y)
  requires x::ll1<> * y::ll1<>
  ensures x'::ll1<>;
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
