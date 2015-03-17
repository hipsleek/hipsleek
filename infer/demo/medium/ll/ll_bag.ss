/* Singly Linked List */
/* Given Shape & Size -> Infer Bag Property */

data node {
  int val;
  node next;
}

llN<n> == self=null & n=0
  or self::node<_, q> * q::llN<n-1>;

/******************************************/

void free(node x)
  requires x::node<_,_>
  ensures x=null;

void free_list(node x)
  requires x::llN<_>
  ensures x=null; 
{
  if (x!=null) {
    free_list(x.next);
    free(x);
  }
}

// True if size is 0, false otherwise.
bool empty(node x)
  requires x::llN<_>
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
  requires x::llN<m>
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

// The number of nodes in a singly linked list
int size(node x)
  requires x::llN<m>
  ensures res=m;
{
  int n = 0;
  return size_helper(x, n);
}

// Get the first element in the singly linked list.
int front(node x)
  requires x::node<v,p> * p::llN<_> 
  ensures res=v;
{
  return x.val;
}

void swap(ref node x, ref node y)
  requires x::llN<n> * y::llN<m>
  ensures x'::llN<m> * y'::llN<n>;
{
  node tmp = x;
  x = y;
  y = tmp;
}

// Erase current content and add n elements with the same value v
void assign(ref node x, int n, int v)
  requires x::llN<n1>
  ensures x'::llN<m> & m=n;
{
  x = create_list(n, v);
}

void push_front(ref node x, int v)
  requires x::llN<n>
  ensures x'::node<v,p> * p::llN<n>;
{
  node tmp = new node(v,x);
  x = tmp;
}

// Get first node
node pop_front(ref node x)
  requires x::node<v,p> * p::llN<n>
  ensures x'::llN<n> * res::node<v,null> & x'=p;
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}

/* Append a singly linked list */
void append(node x, node y)
  requires x::llN<n> * y::llN<m> & x!=null
  ensures x::llN<z> & z=n+m;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* Get the head of a singly linked list */
node ret_first(node x)
  requires x::llN<n>
  ensures x::llN<n>;
{
  return x;
}

/* Get the tail of a singly linked list */
node get_next(node x)
  requires x::node<v,p> * p::llN<n> 
  ensures x::node<v,null> * res::llN<n> & res=p;
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/* Set the tail of a list */
void set_next(node x, node y)
  requires x::llN<_> * y::llN<n> & x!=null
  ensures x::node<_,y> * y::llN<n>;
{
  x.next = y;
}

/* Set the tail to be null */
void set_null(node x)
  requires x::llN<_> & x!=null
  ensures x::node<_,null>;
{
  x.next = null;
}

/* Set the tail to be null */
void set_null2(node x)
  requires x::llN<_> & x!=null
  ensures x::node<_,null>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* Get the third node of a singly linked list */
node get_next_next(node x)
  requires x::node<_,p1> * p1::node<_,p2> * p2::llN<n>
  ensures res::llN<n> & res=p2;
{
  return x.next.next;
}

/* Insert "a" into a non-null singly linked list */
void insert(node x, int a)
  requires x::llN<n> & x!=null
  ensures x::llN<m> & m=n+1;
{
  if (x.next == null)
    x.next = new node(a, null);
  else
    insert(x.next, a);
}


/* Delete the i_th node in a singly linked list */
void del_index(node x, int i)
  requires x::llN<n> & 1<=i<n
  ensures x::llN<m> & n=1+m;
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
  requires x::llN<n>
  ensures res::llN<m> & n>=m>=n-1;
{
  if (x == null)
    return x;
  else
  {
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

/* Create a singly linked list */
node create_list(int n, int v)
  requires true 
  ensures res::llN<m> & m=n;
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

/* Reverse a singly linked list */
void reverse(ref node xs, ref node ys)
  requires xs::llN<n> * ys::llN<m>
  ensures ys'::llN<n+m> & xs'=null;
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

/* Split a singly linked list into two:
   the first part contains "a" nodes
*/
node del_lseg(node x, int a)
  requires x::llN<n> & n>a>0
  ensures x::llN<n1> * res::llN<n2> & n1+n2=n & n1=a;
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

/* Traverse a singly linked list */
void traverse(node x)
  requires x::llN<n>
  ensures x::llN<m> & m=n;
{
  node t;
  if (x != null) {
    t = x;
    traverse(x.next);
  }
}

/* Copy a singly linked list */
node copy(node x)
  requires x::llN<n>
  ensures x::llN<m> * res::llN<z> & n=m & n=z;
{
  node tmp;
  if (x != null) {
    tmp = copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}


/* Remove the first node which has value v */
void list_remove(node x, int v)
  requires x::llN<n> & x!=null
  ensures x::llN<m> & n>=m>=n-1;
{
  if(x.next != null) {
    if(x.next.val == v) {
      node tmp = x.next;
      x.next = x.next.next;
      free(tmp);
    }
    else {
      list_remove(x.next, v);
    }
  }
}

/* Remove the first node which has value v 
   in a nullable singly linked list
*/
node list_remove2(node x, int v)
  requires x::llN<n>
  ensures res::llN<m> & n>=m>=n-1;
{
  node tmp;
  if(x != null) {
    if(x.val == v) {
      tmp = x;
      x = x.next;
      free(tmp);
    }
    else {
      tmp = list_remove2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}

/* Remove all nodes which have value v 
   in nullable singly linked list
*/
node list_filter(node x, int v)
  requires x::llN<n>
  ensures res::llN<m> & m<=n;
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
  requires x::llN<_>
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

/* Splice 2 singly linked list */
void splice (ref node x, node y)
  requires x::llN<n> * y::llN<m>
  ensures x'::llN<z> & z=n+m;
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
