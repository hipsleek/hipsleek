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
  requires x::sll<n>
  case 
  {
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
  requires x::sll<m>
  ensures SIZEH(res,m,n);
{
  if (x==null)
    return n;
  else
    {
      n = n+ 1;
      return size_helper(x.next, n);
    }
}

relation SIZE(int a, int b).
int size(node x)
  infer[SIZE]
  requires x::sll<n> 
  ensures SIZE(res,n);
{
  int m = 0;
  return size_helper(x, m);
}

// A reference to the first element in the list container.
int front(node x)
  infer[x]
  requires x::sll<m>
  ensures true;
{
  return x.val;
}

void swap(ref node x, ref node y)
  infer @post []
  requires x::sll<n>*y::sll<m> 
  ensures x'::sll<n1>*y'::sll<m1>;
{
  node tmp = x;
  x = y;
  y = tmp;
}

// drop current content, and add n element with v value
relation ASSIGN(int a, int b, int c).
void assign(ref node x, int n, int v)
  infer[ASSIGN]
  requires x::sll<m>
  ensures x'::sll<n1> & ASSIGN(n,n1,m);
{
  x = create_list(n, v);
}

relation PUF(int a, int b).
void push_front(ref node x, int v)
  infer[PUF]
  requires x::sll<n>
  ensures x'::sll<m> & PUF(m,n);
{
  node tmp = new node(v,x);
  x = tmp;
}

//pop and return first element
relation PF(int a, int b).
node pop_front(ref node x)
  infer[x,PF]
  requires x::sll<m> 
  ensures x'::sll<n> & PF(m,n);
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* append two sorted singly linked lists */
relation MRG(int a, int b, int c).
node merge1(ref node x1, node x2)
  infer[MRG]
  requires x1::sll<n1> * x2::sll<n2>
  ensures res::sll<m> & MRG(m,n1,n2);
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
relation RF(int m, int n).
node ret_first(node x)
  infer[RF]
  requires x::sll<n> 
  ensures x::sll<m> & RF(m,n);
{
  return x;
}

/* return the tail of a singly linked list */
relation GN(int a, int b).
node get_next(ref node x)
  infer[x,GN]
  requires x::sll<n> 
  ensures x'::node<v,null>*res::sll<m> & GN(m,n);
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* function to set the tail of a list */
relation SN(int a, int b).
 void set_next(ref node x, node y)
   infer[x,SN]
   requires x::sll<i> * y::sll<j>
   ensures x'::sll<k> & SN(k,j);
{
  node tmp = x;
  tmp.next = null;
  x = insert2(y, tmp);
}

void set_null2(ref node x)
  infer[x]
  requires x::sll<n> 
  ensures x'::node<v,r>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* get the tail of a sorted list */
relation GT(int a, int b).
node get_tail(node x)
  infer[x,GT]
  requires x::sll<n> 
  ensures res::sll<m> & GT(m,n);
{
	return x.next;
}

/* function to set null the tail of a list */
void set_null(ref node x)
  infer[x]
  requires x::sll<n>
  ensures x'::node<v,r>;
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(int a, int b).
node get_next_next(node x)
  infer[n,GNN]
  requires x::sll<n> 
  ensures res::sll<m> & GNN(m,n);
{
  return x.next.next;
}

/* insert an element in a sorted list */
relation INS(int a, int b).
node insert(node x, int v)
  infer[INS]
  requires x::sll<n>
  ensures res::sll<m> & INS(m,n);
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
relation INS2(int a, int b).
node insert2(node x, node vn)
  infer[INS2]
  requires x::sll<n> *  vn::node<v, _>
  ensures res::sll<m> & INS2(m,n);
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
relation DEL(int m, int n, int p).
void delete(node x, int a)
  infer [n,a,DEL]
  requires x::sll<n> 
  ensures x::sll<m> & DEL(m,n,a);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the a-th node in a singly linked list */
relation DEL2(int m, int n).
node delete2(node x, int v)
  infer[DEL2]
  requires x::sll<n> 
  ensures res::sll<m> & DEL2(m,n);
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
relation CRL(int a, int b).
node create_list(int n, int v)
  infer [CRL]
  requires true
  ensures res::sll<m> & CRL(m,n);
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

relation SPLIT(int a, int b, int c, int d).
node split1(ref node x, int a)
  infer[SPLIT,n,a]
  requires x::sll<n>
  ensures x'::sll<n1> * res::sll<n2> & SPLIT(n,a,n1,n2);
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
relation TRAV(int k, int m).
void list_traverse(node x)
  infer [TRAV]
  requires x::sll<n>
  ensures x::sll<m> & TRAV(m,n);
{
  node t;
  if(x != null) {
    t = x;
    list_traverse(x.next);
  }
}

relation CPY(int k, int m).
node list_copy(node x)
  infer [CPY]
  requires x::sll<n>
  ensures x::sll<n> * res::sll<m> & CPY(m,n);
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
relation FIL(int k, int m).
node list_filter2(ref node x, int v)
  infer [FIL]
  requires x::sll<n>
  ensures res::sll<m> & FIL(m,n);
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
relation FGE(int a, int b).
node find_ge(node x, int v)
  infer[x,FGE]
  requires x::sll<n> 
  ensures res = null or res::node<m,_> & FGE(v,m);
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


