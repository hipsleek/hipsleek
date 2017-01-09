/* doubly linked lists */

/* representation of a node */
data node {
	int val; 
	node prev;
	node next;	
}

/* view for a doubly linked list with size and bag */
dll<p,n,S> == self = null & n = 0 & S={}
  or self::node<v ,p , q> * q::dll<self, n-1, S1> & S=union(S1, {v})
	inv n >= 0;


void dispose(ref node x)
  requires x::node<_,_,_>
  ensures x'=null;

void delete_list(ref node x)
  requires x::dll<_,_,_>
  ensures x'=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

//true if the container size is 0, false otherwise.
bool empty(node x)
  requires x::dll<_,_,_>
  ensures true;
{
  if (x == null) return true;
  else return false;
}

//The number of elements that conform the list's content.
int size_helper(node x, ref int n)
  requires x::dll<_,m,_>
  ensures res=m+n;
{
  if (x==null) return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}

int size(node x)
  requires x::dll<_,m,_>
  ensures m=res;
{
  int n = 0;
  return size_helper(x, n);
}

// A reference to the first element in the list container.
int front(node x)
  requires x::node<v,p,q>*q::dll<_,_,_>
  ensures res=v;
{
  return x.val;
}

// A reference to the first element in the list container.
int back(node x)
  requires x::dll<_,_,_>
  ensures true;

void swap(ref node x, ref node y)
  infer @post []
  requires x::dll<_,n,S1>*y::dll<_,m,S2>
  ensures x'::dll<_,m,S3>*y'::dll<_,n,S4>; //S1=S4 & S2=S3
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
void assign(ref node x, int n, int v)
// infer @post []
  requires x::dll<_,m,S3> & n>=0
 case {
  n=0 -> ensures x'=null;//'
  n>0 -> ensures x'::dll<_,n,S4> & forall (_x: _x notin S4 | _x = v);//'
  n<0 -> ensures true;
}
{
  x = create_list1(n, v);
}

relation PUF(bag a, bag b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::dll<_,n,S>
  ensures x'::node<v,_,q>*q::dll<_,n,S1> & PUF(S1,S);//' S1=S
{
  if (x==null) {
    node tmp = new node(v,null,x);
    x = tmp;
  }
  else {
    node tmp = new node(v,x.prev,x);
    x = tmp;
  }
}

//pop and return first element
//FAIL
relation PF(bag a, bag b).
node pop_front(ref node x)
  infer[PF]
  requires x::dll<_,m,S1> & x!=null
  ensures x'::dll<_,m-1,S2> & PF(S1,S2); //S2<subset> S1
{
  node tmp = x;
  if (x.next == null) {
    x = x.next;
    tmp.next=null;
    return tmp;
  }
  else {
    x.next.prev = null;
    x = x.next;
    tmp.next = null;
    return tmp;
  }
}

/*
relation APP(bag a, bag b, bag c).
node append(node x, node y)
  infer [APP]
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, t, S> & t=m+n & APP(S,S1,S2); // S=union(S1,S2)

{
	node tmp;
	if (x == null)
		return y;
	else
	{ 	
		tmp = x.next;
		tmp = append(tmp, y);
		if (tmp != null)
		{
			x.next = tmp; 
			tmp.prev = x;
		}
		else {
			x.next = null;
		}
		return x; 
	}
}


relation APP1(bag a, bag b, bag c).
node append1(node x, node y)
  infer [APP1]
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, t, S> & t=m+n & APP1(S,S1,S2);	// S=union(S1,S2)
{
	if (x == null)
		return y;
	else
	{	
		node tmp = append1(x.next, y);
		if (tmp != null)
			tmp.prev = x;
		x.next = tmp;
		return x;
	}
}
*/
relation APP2(bag a, bag b, bag c).
void append2(node x, node y)
  infer [APP2]
	requires x::dll<q, m, S1> * y::dll<p, n, S2> & m>=1
	ensures x::dll<q, t, S> & t=m+n & APP2(S,S1,S2); //S=Union(S1,S2)
{
	node tmp;
	if (x.next == null) {
		x.next = y;
		if (y != null) {
			y.prev = x;
		}		
	}
	else {
		append2(x.next, y);
	}
}



/* return the first element of a doubly linked list */
node ret_first(node x)
  infer @post []
  requires x::dll<_,n,S1>
  ensures x::dll<_,n,S2>; //S2=S1
{
  return x;
}

/* return the tail of a doubly linked list */
relation GN(bag a, bag b, bag c).
node get_next(ref node x)
  infer[GN]
  requires x::dll<_,n,S> & x!=null
  ensures x'::dll<_,1,S1> * res::dll<_,n-1,S2> & GN(S,S1,S2); //S = union(S1, S2)
{
  node tmp = x.next;
  x.next = null;
  x.prev = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(bag a, bag b).
void set_next(ref node x, node y)
  infer[SN]
  requires x::node<v,_,t>*t::dll<x,_,_>*y::dll<_,j,S> & x!=null
  ensures x::node<v,_,y>*y::dll<_,j,S2> & SN(S,S2); // S2=S
{
  if (y==null) 
    x.next = y;
  else {
    x.next = y;
    y.prev = x;
  }
}

void set_null2(ref node x)
  requires x::dll<_,_,_> & x!=null
  ensures x'::node<_,_,null>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::dll<_,_,_> & x!=null
  ensures x'::node<_,_,null>;
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(bag a, bag b).
node get_next_next(node x)
  infer[GNN]
  requires x::dll<_,n,S> & n > 1
  ensures res::dll<_,n-2,S2> & GNN(S,S2); //S2 subset S
{
  return x.next.next;
}

relation INSERT(bag a, bag b, int c).
void insert(node x, int a)
  infer [INSERT]
  requires x::dll<p, n, S> & x!=null
  ensures x::dll<p, m, S1> & m=n+1 & INSERT(S,S1,a); //& S1=S+{a}
{
  if (x.next == null)
    x.next = new node(a, x, null);
  else 
    insert(x.next, a);
}
/*
/* delete a node from a doubly linked list */
// FAIL
relation DEL(bag a, bag b).
void delete( node x, int a)
  infer [DEL]
  requires x::dll<p,n,S> & n > a & a > 0
  ensures x::dll<p,m,S1> & DEL(S,S1);//S1 subset S
{
	node tmp;
	node tmp_null = null;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			x.next = tmp;
		}
		else
			x.next = tmp_null;
	}
	else {
		delete(x.next, a-1);
	}
}
*/
/* function to delete node val = a in a doubly linked list */
// FAIL
relation DEL2(int a, bag b, bag c).
node delete2(ref node x, int a)
//  infer [DEL2]
  requires x::dll<_,n,S>
  ensures res::dll<_,m,S1> & m<=n & (a notin S & S = S1 | S=union(S1, {a}));//DEL2(a,S,S1);//& (a notin S & S = S1 | S=union(S1, {a}));
{
	if (x == null)
		return x;
	else 
  {
		if (x.val == a) 
    {
      if (x.next!=null)
        x.next.prev = null;
      return x.next;
    }
		else 
    {
      node nn = delete2(x.next, a);
      node nn2 = new node(x.val, null, nn);
      if (nn!=null)
        nn.prev = nn2;
      return nn2;
    }
	}
}


/* function to create a doubly linked list with a nodes */
node create_list1(int n, int v)
  requires n>=0
 case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::dll<_,n,S> & forall (_x: _x notin S | _x = v);
  n < 0 -> ensures true;
}

relation CL(bag a, int b).
node create_list(int n, int v)
//  infer[CL]
  requires n>=0
  case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::dll<_,n,S> & forall (_x: _x notin S | _x = v);//CL(S,v);// forall _x: _x notin S | _x = v;
  n < 0 -> ensures true;
  }
{
  node tmp;
  if (n == 0) {
    return null;
  }
  else {
    n = n - 1;
    tmp = create_list(n, v);
    node nn = new node (v, null, tmp);
    if (tmp==null)
      return nn;
    else {
      tmp.prev = nn;
      return nn;
    }
  }
}

/* function to reverse a doubly linked list */
// FAIL
relation REV(bag a, bag b, bag c).
void reverse(ref node xs, ref node ys)
//  infer [REV]
  requires xs::dll<_,n,S1> * ys::dll<_,m,S2>
  ensures ys'::dll<_,n+m,S> & xs' = null & S=union(S1,S2); //REV(S,S1,S2); //S=union(S1,S2)
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    if (ys!=null)
      ys.prev = xs;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}
/*
/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
relation SPLIT(bag a, bag b, bag c).
node split1(ref node x, int a)
  infer[SPLIT]
  requires x::dll<p,n,S> & a > 0 & n > a
  ensures x'::dll<p,n1,S1>*res::dll<_,n2, S2> & n=n1+n2 & n1>0 & n2>0 & n1=a & SPLIT(S,S1,S2);//'S = union(S1, S2);
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
		bind x to (_, xprev, xnext) in {
			tmp = split1(xnext, a);
		}
		return tmp;
	}
}
*/

/*****************************************/
/*********SMALLFOOT EXAMPLES*************/
relation TRAV(bag a, bag b).
void list_traverse(node x)
  infer [TRAV]
  requires x::dll<p,n,S1>
  ensures x::dll<p,n,S2> & TRAV(S1,S2);//S1=S2
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}

relation CPY(bag a, bag b).
node list_copy(node x)
//  infer [CPY]
  requires x::dll<p,n,S>
  ensures x::dll<p,n,S> * res::dll<_,n,S2> & S=S2;//CPY(S,S2); //S2=S
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    node nn = new node (x.val, null, tmp);
    if (tmp!=null)
      tmp.prev = nn;
    return nn;
  }
  else
    return null;
}

/*function to remove the first node which has value v in doubly linked list*/
void list_remove(node x, int v)
  requires x::dll<p,n,S> & n > 0// & x.val != v
  ensures x::dll<p,m,S2> & m <= n;
{
  if(x.next != null) {
    if(x.next.val == v) {
      node tmp = x.next;
      if (x.next.next!=null)
        x.next.next.prev = x;
      x.next = x.next.next;
      dispose(tmp);
    }
    else {
      list_remove(x.next, v);
    }
  }
}

/*function to remove the first node which has value v in nullable doubly linked list*/
// FAIL
relation RMV2(bag a, bag b).
node list_remove2(node x, int v)
//  infer[RMV2]
  requires x::dll<p,n,S> & n >= 0
  ensures res::dll<p,m,S2> & m <= n & S2 subset S; //RMV2(S,S2);//S2 subset S
{
  node tmp;
  if(x != null) {
    if(x.val == v) {
      tmp = x;
      if (x.next!=null)
        x.next.prev = x.prev;
      x = x.next;
      dispose(tmp);
    }
    else {
      tmp = list_remove2(x.next, v);
      if (tmp!=null)
        tmp.prev = x;
      x.next = tmp;
    }
  }
  return x;
}

/*function to remove all nodes which have value v in nullable doubly linked list*/
// FAIL
relation FIL(bag a, bag b).
node list_filter2(ref node x, int v)
//  infer [FIL]
  requires x::dll<_,n,S> & n >= 0
  ensures res::dll<_,m,S2> & m <= n & S2 subset S; //FIL(S,S2);//S2 subset S
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
      if (tmp!=null)
        tmp.prev = x;
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
  requires x::dll<_,n,S> & n >= 0
  ensures res = null or res::node<m,_,_> & m > v & FGE(S,m);//{m} <subset> S;
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
// FAIL
relation SPI(bag S1, bag S2, bag S3).
void splice (ref node x, node y)
//  infer[SPI]
  requires x::dll<_,n,S1> * y::dll<_,m,S2>
  ensures x'::dll<_,m+n,S> & S=union(S1,S2); //SPI(S,S1,S2); //S=union(S1,S2)
{
  if(x == null)
    x = y;
  else {
    if(y != null){
      node nx = x.next;
      node ny = y.next;
      x.next = y;
      if (y!=null)
        y.prev = x;
      splice(nx, ny);
      y.next = nx;
      if (nx!=null)
        nx.prev = y;
    }
  }
}

