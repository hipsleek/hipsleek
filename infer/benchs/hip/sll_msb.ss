/* singly linked lists */
//should not run with eps
/* representation of a node */
data node {
	int val;
	node next;
}

void dispose(node x)
  requires x::node<_,_>
  ensures x=null;

/* view for a sorted linked list */
//size + bag for sorted ll
sll1<n, S> == self = null & n = 0 & S={}
  or self::node<v, r> * r::sll1<m, S1> & n=m+1 & S=union(S1, {v})
  // & forall (x: (x notin S1 | v <= x))
  inv n >= 0;

sll2<n, sm, lg> == self = null & n = 0 & sm <= lg
  or (exists qs,ql: self::node<qmin, q> * q::sll2<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin)
	inv n >= 0 & sm <= lg;

void delete_list(ref node x)
  requires x::sll1<n, S>
  ensures x'=null;//'
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

bool empty(node x)
  requires x::sll1<n, S>
 case {n = 0 -> ensures res;//res
  n!= 0 -> ensures !res;//!(res)
}
{
  if (x == null) return true;
  else return false;
}

//The number of elements that conform the list's content.
int size_helper(node x, ref int n)
  requires x::sll1<m, S> & 0<=m
  ensures res=m+n & m>=0;
{
  if (x==null) return n;
  else {
    n = n+ 1;
    return size_helper(x.next, n);
  }
}
int size(node x)
  requires x::sll1<n, _> & 0<=n
  ensures res=n;
{
  int m = 0;
  return size_helper(x, m);
}

//(val)A reference to the first element in the list container.
int front(node x)
  requires x::node<v,p>*p::sll1<m, _>
  ensures res=v;
{
  return x.val;
}

relation SWAP(bag a, bag b, bag c, bag d).
void swap(ref node x, ref node y)
  infer[SWAP]
  requires x::sll1<n,S1>*y::sll1<m,S2> & 0<=n & 0<=m
  ensures x'::sll1<m,S3>*y'::sll1<n, S4> & SWAP(S1,S2,S3,S4);//S1=S4 & S2=S3
{
  node tmp = x;
  x = y;
  y = tmp;
}

relation PUF(bag a, bag b, int b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::sll1<n, S> & forall (a: (a notin S | v <= a))
  ensures x'::sll1<n+1, S1> & PUF(S1,S,v);//'
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first ele
relation PF(bag a, bag b).
node pop_front(ref node x)
  infer[PF]
  requires x::sll1<m, S1> & x!=null//m>=1
  ensures x'::sll1<m-1, S2> & PF(S1,S2);//'S2 subset S1
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two sorted linked lists */
//fail with eps
relation MRG(bag a, bag b, bag c).
node merge1(node x1, node x2)
  infer[MRG]
  requires x1::sll1<n1,S1> * x2::sll1<n2, S2>
  ensures res::sll1<n1+n2, S3> & MRG(S3,S1,S2);// S3 = union(S1, S2)
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
//fail with eps
relation GN(bag a, bag b, int c).
node get_next(ref node x)
  infer[GN]
  requires x::sll1<n,S> & x!=null
  ensures x'::node<v,null> * res::sll1<n-1,S2> & GN(S,S2,v);//S  = union(S1, S2)//'
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
//fail with eps
relation SN(bag a, bag b, int c).
void set_next(ref node x, node y)
  infer[SN]
  requires x::node<v,t>*t::sll1<_,_> * y::sll1<j,S>& x!=null
  ensures x::sll1<k,S2> & k>=1 & k=j+1 & SN(S,S2,v);
{
  node tmp = x;
  tmp.next = null;
  x = insert2(y, tmp);
}

void set_null2(ref node x)
  requires x::sll1<n, xs, xl> & x != null
  ensures x'::node<v,null> & SNULL2(xs,v, sl);//xs<=v & v<=xl;//'
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
  requires x::sll1<n, S> & x != null
  ensures res::sll1<n-1, S1> & GT(S,S1);//S1 subset S;
{
	return x.next;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  requires x::sll1<n, S> & x != null
  ensures x'::node<v,null>;//'
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(bag a, bag b).
node get_next_next(node x)
  infer[GNN]
  requires x::sll1<n, S> & x != null
  ensures res::sll1<n-2,S2> & GNN(S, S2);//S2 subset S;
{
  return x.next.next;
}

/* insert an element in a sorted list */
relation INS(bag a, bag b, int a).
node insert(node x, int v)
  infer [INS]
  requires x::sll1<n, S>
  ensures res::sll1<n + 1, S1> & INS(S,S1,a);//S1=union(S,{v})
{
	node tmp;

	if (x == null)
		return new node(v, null);
	else
	{
		if (v <= x.val)
			return new node(v, x);
		else
		{
			tmp = x.next;
			x.next = insert(tmp, v);
			return x;
		}
	}
}
relation INS2(bag a, bag b, int a).
node insert2(node x, node vn)
  infer[INS2]
  requires x::sll1<n, S> *  vn::node<v, _>
  ensures res::sll1<n+1, S2> & & INS2(S,S1,a);//S1=union(S,{v})
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
relation DEL(bag a, bag b).
void delete(node x, int a)
  infer [DEL]
  requires x::sll1<n,S> & n > a & a > 0
  ensures x::sll1<m, S1> & DEL(S,S1);//'S1 subset S
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the a-th node in a singly linked list */
relation DEL2(int a, bag b, bag c).
node delete2(node x, int v)
  infer[DEL2]
  requires x::sll1<n, S>
  ensures res::sll1<m, S1> & n-1 <= m <= n & DEL2(a,S,S1);
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
	else
      return null;
}

/* function to create a singly linked list with a nodes */
//relation CL(bag a, int b).
node create_list(int n, int v)
//infer[CL]
  requires n>=0 //0<=v
   case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::sll1<n, S> & S={v} //& CL(S,v);//& S={v};
  n<0 -> ensures true;
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

/*****************************************/
/*********SMALLROOT EXAMPLES*************/
relation TRAV(bag a, bag b).
void list_traverse(node x)
  infer [TRAV]
  requires x::sll1<n,S1>
    ensures x::sll2<n,S2> & TRAV(S1,S2);//S1=S2,  TRAV(S1,S2)
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}
//ok
relation CPY(bag a, bag b).
node list_copy(node x)
  infer [CPY]
  requires x::sll2<n,S>
  ensures x::sll2<n,S> * res::sll2<n,S1> & CPY(S,S2);//
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

/*function to remove all nodes which have value v in nullable singly linked list*/
relation FIL(bag a, bag b).
node list_filter2(node x, int v)
  infer [FIL]
  requires x::sll1<n, S>
  ensures res::sll1<m, S2> &  m <= n & FIL(S,S2);
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
relation FGE(bag a, int b).//{m}<subset> S
node find_ge(node x, int v)
  infer[FGE]
  requires x::sll1<n,S> & n >= 0
  ensures res = null or res::node<m,_> & m >= v & FGE(S,m);//m in S;m in S
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

relation SPLIT(bag a, bag b, bag c).
node split1(ref node x, int a)
  infer[SPLIT]
  requires x::sll1<n, S> & a > 0 & n > a
  ensures x'::sll2<n1, S1> * res::sll2<n2, S2> & n = n1 + n2 & n1 > 0 & n2 > 0 &
 SPLIT(S,S1,S2);//S = union(S1, S2);//'
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
