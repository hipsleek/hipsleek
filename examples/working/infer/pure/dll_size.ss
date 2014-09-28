/* doubly linked lists */

/* representation of a node */
data node {
  int val; 
  node prev;
  node next;	
}

/* view for a doubly linked list without size */
dll<p,n> == self = null & n=0
  or self::node<_ ,p , q> * q::dll<self,n-1> 
  inv n>=0;


void dispose(ref node x)
  requires x::node<_,_,_>
  ensures x'=null;

void delete_list(ref node x)
  requires x::dll<_,_>
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
  requires x::dll<_,n>
  case {
    n=0 -> ensures EMPT1(res);//res
    n!=0 -> ensures EMPT2(res);//!(res)
  }
{
  if (x == null) return true;
  else return false;
}

//The number of elements that conform the list's content.
relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[SIZEH]
  requires x::dll<_,m>
  ensures SIZEH(res,m,n);//res=m+n & m>=0
{
  if (x==null) return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}

relation SIZE(int a, int b).
int size(node x)
  infer[SIZE]
  requires x::dll<_,m>
  ensures SIZE(res,m);//n>=0 & n=res
{
  int n = 0;
  return size_helper(x, n);
}

// A reference to the first element in the list container.
relation FRONT(int a, int b).
int front(node x)
  infer[FRONT]
  requires x::node<v,p,q>*q::dll<_,_>
  ensures FRONT(res,v);//res=v
{
  return x.val;
}

// A reference to the first element in the list container.
int back(node x)
  requires x::dll<_,_>
  ensures true;

void swap(ref node x, ref node y)
  infer @post []
  requires x::dll<_,m>*y::dll<_,n>
  ensures x'::dll<_,m1>*y'::dll<_,n1>; // m=m1 & n=n1
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
relation ASSIGN(int a, int b, int c).
void assign(ref node x, int n, int v)
  infer[ASSIGN]
  requires x::dll<_,m>
  ensures x'::dll<_,n1> & ASSIGN(n,n1,m); // m>=0 & n1>=0 & n1=n
{
  x = create_list(n, v);
}

relation PUF(int a, int b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::dll<_,n>
  ensures x'::node<v,_,q>*q::dll<_,m> & PUF(m,n); //m=n
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
relation PF(int a, int b).
node pop_front(ref node x)
  infer[PF]
  requires x::dll<_,m> & x!=null
  ensures x'::dll<_,n> & PF(n,m); // m>=1 & m=n+1
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

/* append 2 doubly linked lists */
/*relation APP(int a, int b, int c).
node append(node x, node y)
  infer [APP]
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, t> & APP(t,m,n); // t=m+n

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

relation APP1(int a, int b, int c).
node append1(node x, node y)
  infer [APP1]
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, t> & APP1(t,m,n);	//t=m+n
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
/* append 2 doubly linked lists */
relation APP2(int a, int b, int c).
void append2(node x, node y)
  infer [APP2]
	requires x::dll<q, m> * y::dll<p, n> & x!=null //m>=1
	ensures x::dll<q, t> & APP2(t,n,m); //t=m+n
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
relation RF(int m, int n).
node ret_first(node x)
  infer[RF]
  requires x::dll<_,m>
  ensures x::dll<_,n> & RF(m,n); //m=n
{
  return x;
}


/* return the tail of a doubly linked list */
relation GN(int m, int n).
node get_next(node x)
  infer[GN]
  requires x::dll<_,n> & x!=null
  ensures x::node<_,null,null> * res::dll<_,m> & GN(m,n); //m>=0 & m+1=n
{
  node tmp = x.next;
  x.next = null;
  x.prev = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(int m, int n).
void set_next(node x, node y)
  infer[SN]
  requires x::dll<_,i> * y::dll<_,j> & x!=null
  ensures x::dll<_,k> & SN(k,j); // k>=1 & k=j+1
{
  if (y==null) 
    x.next = y;
  else {
    x.next = y;
    y.prev = x;
  }
}

void set_null2(ref node x)
  requires x::dll<_,_> & x!=null
  ensures x'::node<_,_,null>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::dll<_,_> & x!=null
  ensures x'::node<_,_,null>;//'
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(int m, int n).
node get_next_next(node x)
  infer[n,GNN]
  requires x::dll<_,n> & x!=null
  ensures res::dll<_,m> & GNN(m,n); //m>=0 & m+2=n
{
  return x.next.next;
}

relation INSERT(int a, int b).
void insert(node x, int a)
  infer [INSERT]
  requires x::dll<p, n> & x!=null  // n>=1
  ensures x::dll<p, m> & INSERT(m,n); //& n>=1 & n+1=m; 
{
  if (x.next == null)
    x.next = new node(a, x, null);
  else 
    insert(x.next, a);
}

/*
/* delete a node from a doubly linked list */
relation DEL(int a, int b, int c).
void delete(node x, int a)
  infer [DEL,n,a]
	requires x::dll<p, n> //& n > a & a > 0 
	ensures x::dll<p, m> & DEL (n,a,m); // n=m+1
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
relation DEL2(int m, int n).
node delete2(ref node x, int a)
  infer[DEL2]
  requires x::dll<_,n> //& 0<=n
  ensures res::dll<_,m> & DEL2(m,n);// EXPLAIN: m>=0 & (m+1)>=n & n>=m ==> n=m | n=m+1
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
node create_list(int n, int v)
  requires true
  ensures res::dll<_,n>;
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
relation REV(int k, int m, int n).
void reverse(ref node xs, ref node ys)
  infer [REV]
  requires xs::dll<p,n> * ys::dll<q,m>
  ensures ys'::dll<_,k> & xs'=null & REV(k,m,n); // m>=0 & k>=m & k=n+m
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
relation SPLIT(int a, int b, int c, int d).
node split1(ref node x, int a)
  infer[SPLIT,n,a]
  requires x::dll<p,n> // 1<=a & a<=n
  ensures x'::dll<p,n1> * res::dll<_,n2> & SPLIT(n,a,n1,n2); // n2>=0 & n>=(1+n2) & n=n1+n2 & n=a+n2
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
relation TRAV(int k, int m).
void list_traverse(node x)
  infer[TRAV]
  requires x::dll<p,n> //0<=n
  ensures x::dll<p,m> & TRAV(m,n); //m>=0 & m=n
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}

relation CPY(int k, int m).
node list_copy(node x)
  infer[CPY]
  requires x::dll<p,n> //0<=n
  ensures x::dll<p,n> * res::dll<_,m> & CPY(m,n); //m>=0 & m=n
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
relation RMV(int k, int m).
void list_remove(node x, int v)
  infer[RMV]
  requires x::dll<p,n> & x!=null // 1<=n
  ensures x::dll<p,m> & RMV(m,n); // m>=1 & (m+1)>=n & n>=m
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
relation RMV2(int k, int m).
node list_remove2(node x, int v)
  infer[RMV2]
  requires x::dll<p,n> //n>=0
  ensures res::dll<p,m> & RMV2(m,n); //m+1)>=n & m>=0 & n>=m
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
relation FIL(int k, int m).
node list_filter2(ref node x, int v)
  infer[FIL]
  requires x::dll<_,n> // n>=0
  ensures res::dll<_,m> & FIL(m,n); //m>=0 & n>=m
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
relation FGE(int k, int m).
node find_ge(node x, int v)
  infer[FGE]
  requires x::dll<_,n>
  ensures res = null or res::node<m,_,_> & FGE(m,v); // m>=(1+v)
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
  requires x::dll<_,n> * y::dll<_,m> // 0<=m & 0<=n
  ensures x'::dll<_,t> & SPLICE(t,m,n); // m>=0 & t>=m & t=n+m
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

