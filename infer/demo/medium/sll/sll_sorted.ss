/* Sorted Singly Linked List */
/* Given Shape & Size -> Infer Sortedness Property */

data node {
  int val;
  node next;
}

sllN<n> == self = null & n=0
  or self::node<_, q> * q::sllN<n-1>;

/******************************************/

void free(node x)
  requires x::node<_,_>
  ensures x=null;

void free_list(node x)
  requires x::sllN<_>
  ensures x=null; 
{
  if (x!=null) {
    free_list(x.next);
    free(x);
  }
}

// True if size is 0, false otherwise.
bool empty(node x)
  requires x::sllN<_>
  case {
    x = null -> ensures res;
    x != null -> ensures !res;
  }
{
  if (x == null)
    return true;
  else
    return false;
}

int size_helper(node x, ref int n)
  requires x::sllN<m>
  ensures res=m+n & res>=n;
{
  if (x == null)
    return n;
  else
  {
    n = n + 1;
    return size_helper(x.next, n);
  }
}

// The number of nodes in a sorted singly linked list
int size(node x)
  requires x::sllN<m>
  ensures res=m;
{
  int n = 0;
  return size_helper(x, n);
}

// Get the first element in the sorted singly linked list.
int front(node x)
  requires x::node<v,p> * p::sllN<_> 
  ensures res=v;
{
  return x.val;
}

void swap(ref node x, ref node y)
  requires x::sllN<n> * y::sllN<m>
  ensures x'::sllN<m> * y'::sllN<n>;
{
  node tmp = x;
  x = y;
  y = tmp;
}

// Erase current content and add n elements with the same value v
void assign(ref node x, int n, int v)
  requires x::sllN<n1>
  ensures x'::sllN<m> & m=n;
{
  x = create_list(n, v);
}

void push_front(ref node x, int v)
  requires x::sllN<n>
  ensures x'::node<v,p> * p::sllN<n>;
{
  node tmp = new node(v,x);
  x = tmp;
}

// Get first node
node pop_front(ref node x)
  requires x::node<v,p> * p::sllN<n>
  ensures x'::sllN<n> * res::node<v,null> & x'=p;
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* Get the head of a sorted singly linked list */
node ret_first(node x)
  requires x::sllN<n>
  ensures x::sllN<n>;
{
  return x;
}

/* Get the tail of a sorted singly linked list */
node get_next(node x)
  requires x::node<v,p> * p::sllN<n> 
  ensures x::node<v,null> * res::sllN<n> & res=p;
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* Set the tail of a list */
void set_next(ref node x, node y)
  requires x::node<_,p> * p::sllN<_> * y::sllN<n>
  ensures x'::sllN<m> & m=n+1;
{
  node tmp = x;
  tmp.next = null;
  x = insert2(y, tmp);
}

/* Set the tail to be null */
void set_null(node x)
  requires x::sllN<_> & x!=null
  ensures x::node<_,null>;
{
  x.next = null;
}

/* Set the tail to be null */
void set_null2(node x)
  requires x::sllN<_> & x!=null
  ensures x::node<_,null>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* Get the third node of a sorted singly linked list */
node get_next_next(node x)
  requires x::node<_,p1> * p1::node<_,p2> * p2::sllN<n>
  ensures res::sllN<n> & res=p2;
{
  return x.next.next;
}

/* Insert "a" into a sorted singly linked list */
node insert(node x, int a)
  requires x::sllN<n>
  ensures res::sllN<m> & m=n+1;
{
  node tmp;

  if (x == null)
    return new node(a, null);
  else
  {
    if (a <= x.val)
      return new node(a, x);
    else
    {
      tmp = x.next;
      x.next = insert(tmp, a);
      return x;
    }
  }
}

/* Insert a node into a sorted singly linked list */
node insert2(node x, node vn)
  requires x::sllN<n> * vn::node<v,_>
  ensures res::sllN<m> & m=n+1;
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

/* Delete the i_th node in a sorted singly linked list */
void del_index(node x, int i)
  requires x::sllN<n> & 1<=i<n
  ensures x::sllN<m> & n=1+m;
{
  if (i == 1)
  {
    node tmp = x.next;
    x.next = x.next.next;
    free(tmp);
  }
  else
  {
    del_index(x.next, i-1);
  }
}


/* Delete the node with value a */
node del_val(node x, int a)
  requires x::sllN<n>
  ensures res::sllN<m> & n>=m>=n-1;
{
  if (x == null)
    return x;
  else
  {
    if (a < x.val)
      return x;
    else
      if (x.val == a)
      {
        node tmp = x.next;
        free(x);
        return tmp;
      }
      else
      {
        x.next = del_val(x.next,a);
        return x;
      }
  }
}

/* Create a sorted singly linked list */
node create_list(int n, int v)
  requires true 
  ensures res::sllN<m> & m=n;
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

/* Split a sorted singly linked list into two:
   the first part contains "a" nodes
*/
node del_lseg(node x, int a)
  requires x::sllN<n> & n>a>0
  ensures x::sllN<n1> * res::sllN<n2> & n1+n2=n & n1=a;
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
      tmp = del_lseg(xnext, a);
    }
    return tmp;
  }
}

/********* SMALLFOOT EXAMPLES *************/

/* Traverse a sorted singly linked list */
void traverse(node x)
  requires x::sllN<n>
  ensures x::sllN<m> & m=n;
{
  node t;
  if (x != null) {
    t = x;
    traverse(x.next);
  }
}

/* Copy a sorted singly linked list */
node copy(node x)
  requires x::sllN<n>
  ensures x::sllN<m> * res::sllN<z> & n=m & n=z;
{
  node tmp;
  if (x != null) {
    tmp = copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}


/* Remove all nodes which have value v 
   in nullable sorted singly linked list
*/
node list_filter(node x, int v)
  requires x::sllN<n>
  ensures res::sllN<m> & m<=n;
{
  node tmp;
  if(x != null) {
    if(x.val == v){
      tmp = x.next;
      free(x);
      x = tmp;
      x = list_filter(x,v);
    }
    else{
      tmp = list_filter(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}

/******** SLAYER EXAMPLES **********/

/* Get the first node greater than v */
node find_ge(node x, int v)
  requires x::sllN<_>
  ensures res = null or res::node<m,_> & m>v;
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

/* Merge two sorted singly linked lists */
node merge(node x1, node x2)
  requires x1::sllN<n> * x2::sllN<m>
  ensures res::sllN<z> & z=n+m;
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
        return merge(x1, x2.next);
      else
        return x1;
    }
  }
}
