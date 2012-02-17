/* singly linked lists */

/* representation of a node */

data node {
	int val;
	node next;
}

void dispose(node x)
  requires x::node<_,_>
  ensures x=null;

/* view for a singly linked list */

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});

void delete_list(node x)
  requires x::ll2<n,S>
   ensures x=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

/*ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

/* append two singly linked lists */
relation APP(bag a, bag b, bag c).
void append(node x, node y)
  infer @pre [APP]
  requires x::ll2<n1,S1> * y::ll2<n2,S2> & x!=null//S1=1
  ensures x::ll2<m,S> & m=n1+n2 & APP(S,S1,S2);//S=union(S1,S2) & S1=1
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* return the first element of a singly linked list */
relation RF(bag a, bag b).
node ret_first(node x)
  infer [RF]
  requires x::ll2<n,S1>
  ensures x::ll2<n,S2> & RF(S1,S2);//S2=S1
{
  return x;
}

/* return the tail of a singly linked list */
relation GN(bag a, bag b, bag c).
node get_next(ref node x)
  infer[GN]
  requires x::ll2<n,S> & x!=null
  ensures x'::ll2<1,S1> * res::ll2<n-1,S2> & GN(S,S1,S2);//S  = union(S1, S2)//'
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(bag a, bag b, int c).
 void set_next(ref node x, node y)
   infer[SN]
   requires x::node<v,t>*t::ll2<_,_> * y::ll2<j,S>& x!=null
   ensures x::ll2<k,S2> & k>=1 & k=j+1 & SN(S,S2,v);
{
	x.next = y;
}

void set_null2(ref node x)
  requires x::ll2<i,_> & x!=null
  ensures x'::ll2<1,_>;//'
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::ll2<i,S> & x!=null
   ensures x'::node<_,null>;//'
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(bag a, bag b).
node get_next_next(node x)
//infer[GNN]
  requires x::ll2<n,S> & n > 1
  ensures res::ll2<n-2,S2> & S2 subset S;//GNN(S,S2);//S2 subset S;
{
  return x.next.next;
}

/* function to insert a node in a singly linked list */
relation INS(bag a, bag b, int a).
void insert(node x, int a)
  infer @pre [INS]
  requires x::ll2<n,S> & n > 0
  ensures x::ll2<n+1,S1> & INS(S,S1,a);//S=1 & S1=2 & S1=2
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
  infer[DEL]
  requires x::ll2<n,S> & n > a & a > 0
  ensures x::ll2<m,S1> & DEL(S,S1);//'
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to create a singly linked list with a nodes */
relation CL(bag a).
node create_list(int a)
  infer[CL]
  requires a >= 0
  ensures res::ll2<a,S> & CL(S);
{
  node tmp;
  if (a == 0) {
    return null;
  }
  else {
    a  = a - 1;
    tmp = create_list(a);
    return new node (0, tmp);
  }
}

/* function to reverse a singly linked list */
relation REV(bag a, bag b, bag c).
void reverse(ref node xs, ref node ys)
  infer [REV]//
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
/*****************************************/
/*********SMALLROOT EXAMPLES*************/
relation TRAV(bag a, bag b).
  void list_traverse(node x)
  infer @pre [TRAV]
  requires x::ll2<n,S1>
  ensures x::ll2<n,S2> & TRAV(S1,S2);//S1=S2 good
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
   infer @pre [CPY]
  requires x::ll2<n,S>
  ensures x::ll2<n,S> * res::ll2<n,S2> &  CPY(S,S2);//S2=S good
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
  requires x::ll2<n,S> & n > 0// & x.val != v
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
  infer[FIL]
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
    else{
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
void splice (ref node x, node y)
  requires x::ll2<n,S1> * y::ll2<m,S2>
  ensures x'::ll2<m+n,S>;//'
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
