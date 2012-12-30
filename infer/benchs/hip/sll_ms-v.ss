/* sorted singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a sorted singly linked list */
sll<n> == self = null & n = 0
  or self::node<_, q> * q::sll<n-1>
	inv n >= 0;


void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

relation A (node x).
void delete_list(ref node x)
  infer [A]
  requires x::sll<n>
  ensures A(x'); //x'=null
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

//true if the container size is 0, false otherwise.
//relation EMPT1(bool a).
//relation EMPT2(bool a).
bool empty(node x)
//infer[EMPT1,EMPT2]
  requires x::sll<n>
  case
  {
    n = 0 -> ensures res;//res
    n!= 0 -> ensures !res;//!(res)
  }
{
  if (x == null)
    return true;
  else
    return false;
}

//The number of elements that conform the list's content.
//relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
//infer[SIZEH]
  requires x::sll<m>
  ensures res=m+n;
{
  if (x==null)
    return n;
  else
    {
      n = n+ 1;
      return size_helper(x.next, n);
    }
}

//relation SIZE(int a, int b).
int size(node x)
//infer[SIZE]
  requires x::sll<n> //& 0<=n
  ensures res=n;
{
  int m = 0;
  return size_helper(x, m);
}

// A reference to the first element in the list container.
int front(node x)
// infer[x]
  requires x::sll<m> &x!=null
  ensures true;//res=Anon_1027 
{
  return x.val;
}

void swap(ref node x, ref node y)
//infer @post []
  requires x::sll<n>*y::sll<m> //& 0<=n & 0<=m
  ensures x'::sll<n1>*y'::sll<m1> & n1>=0 & m1>=0 & n1=m & m1=n;
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
//relation ASSIGN(int a, int b, int c).
void assign(ref node x, int n, int v)
//infer[ASSIGN]
  requires x::sll<m>
  ensures x'::sll<n> ;//'& ASSIGN(n,n1,m);
{
  x = create_list(n, v);
}

//relation PUF(int a, int b).
void push_front(ref node x, int v)
//infer[PUF]
  requires x::sll<n>
  ensures x'::sll<m> &m=n+1 & m>=1;//'
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first element
//relation PF(int a, int b).
node pop_front(ref node x)
//infer[x,PF]
  requires x::sll<m> & m>=1 & x!=null
  ensures x'::sll<n> & n>=0 & n+1=m;//PF(m,n);//'& n>=0 & n+1=m
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two sorted singly linked lists */
//relation MRG(int a, int b, int c).
node merge1(ref node x1, node x2)
//infer[MRG]
  requires x1::sll<n1> * x2::sll<n2>
  ensures res::sll<m> & m=n1+n2;//MRG(m,n1,n2);//m=n1+n2
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

/* return the first element of a sorted singly linked list */
//relation RF(int m, int n).
node ret_first(node x)
//infer[RF]
  requires x::sll<n> //& 0<=n
  ensures x::sll<m> & m>=0 & m=n;//RF(m,n);//m>=0 & m=n
{
  return x;
}

/* return the tail of a singly linked list */
//relation GN(int a, int b).
node get_next(ref node x)
// infer[x,GN]
  requires x::sll<n> & x != null
  ensures x'::node<v,null>*res::sll<m> & n>=1 & n=m+1;//GN(m,n);//'//n>=1 & n=m+1
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
//relation SN(int a, int b).
 void set_next(ref node x, node y)
 // infer[x,SN]
   requires x::sll<i> * y::sll<j> & x!=null
   ensures x'::sll<j+1>;// & SN(k,j); //'
{
  node tmp = x;
  tmp.next = null;
  x = insert2(y, tmp);
}

void set_null2(ref node x)
//infer[x]
  requires x::sll<n> & x != null
  ensures x'::node<v,null>;//'r=null
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* get the tail of a sorted list */
//relation GT(int a, int b).
node get_tail(node x)
//infer[x,GT]
  requires x::sll<n> & x != null & n>=1
  ensures res::sll<m> & n=m+1;//GT(m,n);//n=m+1
{
	return x.next;
}

/* function to set null the tail of a list */
void set_null(ref node x)
//infer[x]
  requires x::sll<n> & x != null
  ensures x'::node<v,null>;//'r=null
{
  x.next = null;
}

/* function to get the third element of a list */
//relation GNN(int a, int b).
node get_next_next(node x)
//infer[n,GNN]
  requires x::sll<n> & x != null & 2<=n
  ensures res::sll<m> & n>=2 & n=m+2;//GNN(m,n);//n>=2 & n=m+2
{
  return x.next.next;
}

/* insert an element in a sorted list */
//relation INS(int a, int b).
node insert(node x, int v)
//infer[INS]
  requires x::sll<n>
  ensures res::sll<m> & m=n+1;//INS(m,n);//m=n+1
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

/* insert a node into a sorted list */
//relation INS2(int a, int b).
node insert2(node x, node vn)
//infer[INS2]
  requires x::sll<n> *  vn::node<v, _>
  ensures res::sll<m> & m=n+1;//INS2(m,n);//m=n+1
{
	if (x==null) 
  {
		vn.next = null;
		return vn;
	}
	else
  if (vn.val <= x.val) 
  {
	  vn.next = x;
	  return vn;
  }
  else
  {
	  x.next = insert2(x.next, vn);
	  return x;
  }
}

/* function to delete the a-th node in a sorted singly linked list */
//relation DEL(int m, int n, int p).
void delete(node x, int a)
//infer [n,a,DEL]
  requires x::sll<n> & a>=1 & a<n
  ensures x::sll<m> & m=n-1;
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the a-th node in a singly linked list */
//relation DEL2(int m, int n).
node delete2(node x, int v)
// infer[DEL2]
  requires x::sll<n> //0<=n
  ensures res::sll<m> & m>=0 & (m+1)>=n & n>=m;//DEL2(m,n);//m>=0 & (m+1)>=n & n>=m ==> n=m | n=m+1
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
node create_list(int n, int v)
  requires true
  ensures res::sll<n>;
{
  node tmp;
  if (n == 0)
  {
    return null;
  }
  else {
    n  = n - 1;
    tmp = create_list(n,v);
    return new node (v, tmp);
  }
}

/*
/* function to reverse a singly linked list */
//relation REV(node x, int k, int m, int n).
void reverse(ref node xs, ref node ys)
//  infer[REV]
  requires xs::ll<n> * ys::ll<m> //0<=m & 0<=n
  ensures ys'::ll<k> &  xs' = null & m>=0 & k>=m & k=n+m;//REV(xs',k,m,n);// xs' = null & m>=0 & k>=m & k=n+m
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

*/

//relation SPLIT(int a, int b, int c, int d).
node split1(ref node x, int a)
//infer[SPLIT,n,a]
  requires x::sll<n> & a<n & a>=1
  ensures x'::sll<n1> * res::sll<n2> & n1>=1 & n2>=1 & n1+n2=n;//SPLIT(n,a,n1,n2);//'n1>=1 & n2>=1 & n1+n2=n
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
/*********SMALLROOT EXAMPLES*************/
//relation TRAV(int k, int m).
void list_traverse(node x)
//  infer [TRAV]
  requires x::sll<n>
  ensures x::sll<n> ;//& TRAV(m,n);//m=n
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}

//relation CPY(int k, int m).
node list_copy(node x)
//infer [CPY]
  requires x::sll<n>
  ensures x::sll<n> * res::sll<n> ;//& CPY(m,n);//m=n
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

/*
/*function to remove the first node which has value v in singly linked list*/
//relation RMV(int k, int m).
void list_remove(node x, int v)
//  infer[RMV]
  requires x::ll<n> & x!=null // 1<=n
  ensures x::ll<m> & m>=1 & (m+1)>=n & n>=m;//RMV(m,n); // m>=1 & (m+1)>=n & n>=m
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
//relation RMV2(int k, int m).
node list_remove2(node x, int v)
//  infer[RMV2]
  requires x::ll<n> //n>=0
  ensures res::ll<m> & (m+1)>=n & m>=0 & n>=m;//RMV2(m,n); //m+1)>=n & m>=0 & n>=m
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
*/
/*function to remove all nodes which have value v in nullable singly linked list*/
//relation FIL(int k, int m).
node list_filter2(ref node x, int v)
//  infer [FIL]
  requires x::sll<n>
  ensures res::sll<m> & m<=n;//FIL(m,n);
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
//relation FGE(int a, int b).
node find_ge(node x, int v)
//  infer[x,FGE]
  requires x::sll<n> //& n >= 0
  ensures res = null or res::node<m,_> & m>=v;//FGE(v,m);//m>=v
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


