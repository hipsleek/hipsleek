/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a sorted linked list */
sll2<n, sm, lg, S> == self = null & n = 0 & sm <= lg & S={}
  or (exists qs,ql: self::node<qmin, q> * q::sll2<n-1, qs, ql, S1> & qmin <= qs & ql <= lg & sm <= qmin & S=union(S1, {qmin}))
	inv n >= 0 & sm <= lg;

sll1<n, sm, lg, S> == self = null & n = 0 & sm <= lg & S={}
  or (exists qs,ql: self::node<qmin, q> * q::sll1<n-1, qs, ql, S1> & qmin <= qs & ql = lg & sm = qmin  & S=union(S1, {qmin}))
	inv n >= 0 & sm <= lg;

node ret_null(node x)
  requires x::sll1<0,sm,lg,S>
  ensures res::sll1<0,sm,lg,S>;
{
  return x;
}

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

void delete_list(ref node x)
  requires x::sll2<n, sm, lg, _>
  ensures x'=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

bool empty(node x)
  requires x::sll2<n, sm, lg, _>
  case 
  {
    n = 0 -> ensures res;
    n!= 0 -> ensures !res;
  }
{
  if (x == null) return true;
  else return false;
}

//The number of elements that conform the list's content.
int size_helper(node x, ref int n)
  requires x::sll2<m, sm, lg, _>
  ensures res=m+n;
{
  if (x==null) return n;
  else {
    n = n+ 1;
    return size_helper(x.next, n);
  }
}
int size(node x)
  requires x::sll2<n, sm, lg, _>
  ensures res=n;
{
  int m = 0;
  return size_helper(x, m);
}

// A reference to the first element in the list container.
int front(node x)
  requires x::node<v,p>*p::sll2<m, sm, lg,_>
  ensures res=v;
{
  return x.val;
}

void swap(ref node x, ref node y)
  infer @post []
  requires x::sll2<n,sm1, lg1, S1>*y::sll2<m,sm2, lg2, S2>
  ensures x'::sll2<m,smy2, lgy2, S3>*y'::sll2<n, smx1, lgx1, S4> ;
{
  node tmp = x;
  x = y;
  y = tmp;
}

void push_front(ref node x, int v)
  requires x::sll2<n, sm, lg, S> & v <=sm & forall (a: (a notin S | v <= a))
  ensures x'::sll2<n+1, v, lg1, S1> & forall (a2: (a2 notin S1 | v <= a2));
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first element
relation PF(bag a, bag b).
node pop_front(ref node x)
  infer[PF]
  requires x::sll2<m, sm1, lg1, S1> & x!=null
  ensures x'::sll2<m-1, sm2, lg2, S2> & sm1<=sm2 & lg2<=lg1 & PF(S1,S2);//'
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* return the tail of a singly linked list */
relation GN(bag a, bag b, int c).
node get_next(ref node x)
  infer[GN]
  requires x::sll2<n, xs, xl, S> & x != null
  ensures x'::node<v,null>*res::sll2<n-1, sres, lres, S2> & sres >= xs & lres <= xl & xs<=v & v<=sres & GN(S,S2,v);
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(bag a, bag b, int c).
void set_next(ref node x, node y)
  requires x::node<v,t>*t::sll2<_,sm1, lg1, _> * y::sll2<j,sm2, lg2, S>
  ensures x'::sll2<k, sm3, lg3, S2> & k=j+1 & sm3=min(sm2,v) & lg3=max(lg2,v) & S2=union(S,{v});

void set_null2(ref node x)
  requires x::sll2<n, xs, xl,_> & x != null
  ensures x'::node<v,null> & xs<=v & v<=xl;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* get the tail of a sorted list */
relation GT(bag a, bag b).
node get_tail(node x)
  infer[GT]
  requires x::sll2<n, xs, xl, S> & x != null 
  ensures res::sll2<n-1, sres, lres, S1> & sres >= xs & lres <= xl & GT(S,S1);
{
	return x.next;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::sll2<n, xs, xl, _> & x != null
  ensures x'::node<v,null> & xs<=v & v<=xl;
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(bag a, bag b).
node get_next_next(node x)
  infer[GNN]
  requires x::sll2<n, sm1, lg1, S1> & n>1
  ensures res::sll2<n-2,sm2, lg2, S2> & sm2>=0 & sm2>=sm1 & lg2>=sm2 & lg1>=lg2 & GNN(S1,S2);
{
  return x.next.next;
}

/* insert an element in a sorted list */
relation INS(int a, int b, int c, int d, int e).
node insert(node x, int v)
	requires x::sll2<n, sm, lg, S>
	ensures res::sll2<n+1, mi, ma, S1> & mi=min(v,sm) & ma=max(v,lg) & S1=union(S,{v});

relation INS2(int a, int b, int c).
node insert2(node x, node vn)
  requires x::sll2<n, sm, lg, S1> * vn::node<v, _>
  ensures res::sll2<n+1, mi, ma, S2> & mi=min(v, sm) & ma=max(v, lg) & S2=union(S1,{v});

/* function to delete the a-th node in a singly linked list */
relation DEL(bag a, bag b).
void delete(node x, int a)
  infer[DEL]
  requires x::sll1<n,xs, xl, S> & n > a & a > 0
  ensures x::sll1<nres, sres, lres, S1> & nres = n-1 & sres >= xs & lres <= xl & DEL(S1,S);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the a-th node in a singly linked list */
relation DEL2(bag a, bag b, int c).
node delete2(node x, int v)
  infer[DEL2]
  requires x::sll1<n, xs, xl, S>
  ensures res::sll1<nres, sres, lres, S1> & n-1 <= nres <= n & sres >= xs & lres <= xl & DEL2(S1,S,v);
{
	node tmp;

	if (x != null)
    if (v < x.val)
      return x;
    else
    if (v == x.val)
      return x.next;
    else
    {
      tmp = x.next;
      x.next = delete2(tmp, v);
      return x;
    }
	else{
    assume sres = xs;
    assume lres = xl;
    return null;
  }
}

/* function to create a singly linked list with a nodes */
relation CL(int a, bag b).
node create_list(int n, int v)
  requires n>=0
  case 
  {
    n = 0 -> ensures res=null;
    n > 0 -> ensures res::sll1<n, sm, lg, S> & sm=v & v=lg & forall (_x: _x notin S | _x=v);
    n < 0 -> ensures true;
  }
{
  node tmp;
  if (n == 0) {
    return null;
  }
  else {
    n  = n - 1;
    tmp = create_list(n,v);
    return new node (v, tmp);
  }
}

relation SPLIT(bag a, bag b, bag c).
node split1(ref node x, int a)
  infer[SPLIT]
  requires x::sll2<n,sm,sl,S> & a > 0 & n > a
  ensures x'::sll2<n1,sm1,sl1,S1> * res::sll2<n2,sm2,sl2,S2> & n=n1+n2 & n1 = a & sm1=sm & SPLIT(S,S1,S2);
{
  node tmp;

  if (a == 1)	{
    tmp = x.next;
    x.next = null;
    return tmp;
  }
  else{
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
  requires x::sll1<n,sm1, lg1, S1>
  ensures x::sll1<n,sm1, lg1, S2> & TRAV(S1,S2);
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
  requires x::sll1<n,sm1, lg1, S1>
  ensures x::sll1<n,sm1, lg1, S1> * res::sll1<n,sm1, lg1, S2> & CPY(S1,S2);
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else {
    assume sm2=sm1;
    assume lg2=lg1;
    return null;
  }
}

/*function to remove all nodes which have value v in nullable singly linked list*/
relation FIL(bag a, bag b).
node list_filter2(node x, int v)
  requires x::sll1<n, xs, xl, S>
  ensures res::sll1<nres, sres, lres, S2> & nres <= n & lres <= xl & sres >= xs & S2 subset S;
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
  else {
    assume lres=xl;
    assume sres=xs;
  }
  return x;
}

/**************************************************************/
/**********************SLAYER (SLL) EXAMPLES***************************/
/* function to return the first node being greater than v*/
relation FGE(bag a, int b).
node find_ge(node x, int v)
  infer[FGE]
  requires x::sll2<n,sm,sl,S> & n >= 0
  ensures res = null or res::node<m,p>*p::sll2<k,sm2,sl2,_> & m >= v & m<=sl2 & FGE(S,m);
{
  if(x == null)
    return null;
  else {
    if(x.val >= v)
      return x;
    else
      return find_ge(x.next, v);
  }
}
