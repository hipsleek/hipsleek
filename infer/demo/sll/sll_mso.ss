/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a sorted linked list */
sll2<n, sm, lg> == self = null & n = 0 & sm <= lg
  or (exists qs,ql: self::node<qmin, q> * q::sll2<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin)
	inv n >= 0 & sm <= lg;

sll1<n, sm, lg> == self = null & n = 0 & sm <= lg
  or (exists qs,ql: self::node<qmin, q> * q::sll1<n-1, qs, ql> & qmin <= qs & ql = lg & sm = qmin)
	inv n >= 0 & sm <= lg;

node ret_null(node x)
  requires x::sll1<0,sm,lg>
  ensures res::sll1<0,sm,lg>;
{
  return x;
}

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

void delete_list(ref node x)
  requires x::sll2<n, sm, lg>
  ensures x'=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

bool empty(node x)
  requires x::sll2<n, sm, lg>
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
  requires x::sll2<m, sm, lg>
  ensures res=m+n;
{
  if (x==null) return n;
  else {
    n = n+ 1;
    return size_helper(x.next, n);
  }
}
int size(node x)
  requires x::sll2<n, sm, lg>
  ensures res=n;
{
  int m = 0;
  return size_helper(x, m);
}

// A reference to the first element in the list container.
int front(node x)
  requires x::node<v,p>*p::sll2<m, sm, lg>
  ensures res=v;
{
  return x.val;
}

void swap(ref node x, ref node y)
  infer @post []
  requires x::sll2<n,sm1, lg1>*y::sll2<m,sm2, lg2>
  ensures x'::sll2<m,smy2, lgy2>*y'::sll2<n, smx1, lgx1> ;
{
  node tmp = x;
  x = y;
  y = tmp;
}

relation PUF(int a, int b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::sll2<n, sm, lg> & PUF(v,sm)
  ensures x'::sll2<n+1, v1, lg1>;
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first ele
relation PF(int a, int b, int c, int d).
node pop_front(ref node x)
  infer[PF]
  requires x::sll2<m, sm1, lg1> & x!=null
  ensures x'::sll2<m-1, sm2, lg2> & PF(sm1,sm2,lg1,lg2);
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two singly linked lists */
relation MRG(int a, int b, int c, int d, int e, int f).
node merge1(node x1, node x2)
  infer[MRG]
  requires x1::sll2<n1,sm1, lg1> * x2::sll2<n2, sm2, lg2>
  ensures res::sll2<n1+n2, sm3, lg3> & MRG(sm1,sm2,sm3,lg1,lg2,lg3);
{
	if (x2 == null)
		return x1; 
	else
	{
		if (x1 == null)
			return x2;
		else
		{
			x1 = insert(x1, x2.val);
			if (x2.next != null)
				return merge1(x1, x2.next);
			else
				return x1;
		}
	}
}

/* return the tail of a singly linked list */
relation GN(int a, int b, int c, int d).
node get_next(ref node x)
  infer[GN]
  requires x::sll2<n, xs, xl> & x != null
  ensures x'::node<v,null>*res::sll2<n-1, sres, lres> & GN(sres,xs,lres,xl) & xs<=v & v<=sres;
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(int a, int b, int c, int d, int e).
void set_next(ref node x, node y)
  infer[SN]
  requires x::node<v,t>*t::sll2<_,sm1, lg1> * y::sll2<j,sm2, lg2>
  ensures x'::sll2<k, sm3, lg3> & k=j+1 & SN(v,sm2,sm3,lg3m,lg2);
{
  node tmp = x;
  tmp.next = null;
  x = insert2(y, tmp);
}

relation SNULL2(int a, int b, int c).
void set_null2(ref node x)
  infer[SNULL2]
  requires x::sll2<n, xs, xl> & x != null
  ensures x'::node<v,null> & SNULL2(xs,v,sl);
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* get the tail of a sorted list */
relation GT(int a, int b, int c, int d).
node get_tail(node x)
  infer[GT]
  requires x::sll2<n, xs, xl> & x != null 
  ensures res::sll2<n-1, sres, lres> & GT(sres,xs,lres,xl);
{
	return x.next;
}

/* function to set null the tail of a list */
relation SNULL(int a, int b, int c).
void set_null(ref node x)
  infer[SNULL]
  requires x::sll2<n, xs, xl> & x != null
  ensures x'::node<v,null> & SNULL(xs,v, sl);
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(int a, int b, int c, int d).
node get_next_next(node x)
  infer[n,GNN]
  requires x::sll2<n, sm1, lg1>
  ensures res::sll2<n-2,sm2, lg2> & GNN(sm1, lg1,sm2, lg2);
{
  return x.next.next;
}

/* insert an element in a sorted list */
relation INS(int a, int b, int c, int d, int e).
node insert(node x, int v)
	requires x::sll2<n, sm, lg>
	ensures res::sll2<n+1, mi, ma> & mi=min(v,sm) & ma=max(v,lg);
{
	node tmp;

	if (x == null){
		return new node(v, null);
  }
	else
	{
		if (v <= x.val){
			return new node(v, x);
    }
		else
		{
			tmp = x.next;
			x.next = insert(tmp, v);
			return x;
		}
	}
}

relation INS2(int a, int b, int c).
node insert2(node x, node vn)
  requires x::sll2<n, sm, lg> * vn::node<v, _>
  ensures res::sll2<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		vn.next = null;
		return vn;
	}
	else if (vn.val <= x.val) {
		vn.next = x;
		return vn;
	}
	else {
		x.next = insert2(x.next, vn);
		return x;
	}
}

/* function to delete the a-th node in a singly linked list */
relation DEL(int a, int b, int c, int d).
void delete(node x, int a)
  infer[DEL]
  requires x::sll1<n,xs, xl> & n > a & a > 0
  ensures x::sll1<nres, sres, lres> & nres = n-1 & DEL(sres,xs,lres,xl);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the a-th node in a singly linked list */
relation DEL2(int a, int b, int c, int d).
node delete2(node x, int v)
  infer[DEL2]
  requires x::sll1<n, xs, xl> 
  ensures res::sll1<nres, sres, lres> & n-1 <= nres <= n & DEL2(sres,xs,lres,xl);
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
relation CL(int a, int b, int c).
node create_list(int n, int v)
  infer[CL]
  requires n>=0
  case 
  {
    n = 0 -> ensures res=null;
    n > 0 -> ensures res::sll1<n, sm, lg> & CL(sm,lg,v);
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

relation SPLIT(int a, int b, int c, int d).
node split1(ref node x, int a)
  requires x::sll2<n,sm,sl> & a > 0 & n > a
  ensures x'::sll2<n1,sm1,sl1> * res::sll2<n2,sm2,sl2> & n=n1+n2 & n1>0 & n2>0 & n1 = a & sl1 <= sm2 & sm1=sm;
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
relation TRAV(int a, int b, int c, int d).
void list_traverse(node x)
  infer [TRAV]
  requires x::sll1<n,sm1, lg1>
  ensures x::sll1<n,sm2, lg2> & TRAV(sm1,lg1,sm2,lg2);
{
  node t;
  if(x != null) {
    t = x;
    list_traverse(x.next);
  }
}

relation CPY(int a, int b, int c, int d).
node list_copy(node x)
  infer [CPY]
  requires x::sll1<n,sm1, lg1>
  ensures x::sll1<n,sm1, lg1> * res::sll1<n,sm2, lg2> & CPY(sm1, lg1,sm2, lg2);
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
relation FIL(int a, int b, int c, int d).
node list_filter2(node x, int v)
  infer [FIL]
  requires x::sll1<n, xs, xl>
  ensures res::sll1<nres, sres, lres> & nres <= n & FIL(xs,xl,sres,lres);
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
relation FGE(int a, int b).
node find_ge(node x, int v)
  infer[FGE]
  requires x::sll2<n,sm,sl> & n >= 0
  ensures res = null or res::node<m,p>*p::sll2<k,sm2,sl2> & m >= v & FGE(m,sl2);
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

