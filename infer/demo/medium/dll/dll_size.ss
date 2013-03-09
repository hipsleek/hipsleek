/* Doubly Linked List */
/* Given Shape -> Infer Size Property */

data node2 {
  int val;
  node2 prev;
  node2 next;
}

dll<p> == self = null
  or self::node2<_,p,q> * q::dll<self>;

/******************************************/

void free(node2 x)
  requires x::node2<_,_,_>
  ensures x=null;

void free_list(node2 x)
  requires x::dll<_>
  ensures x=null; 
{
  if (x!=null) {
    free_list(x.next);
    free(x);
  }
}

// True if size is 0, false otherwise.
bool empty(node2 x)
  requires x::dll<_>
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

int size_helper(node2 x, ref int n)
  requires x::dll<_>
  ensures true;
{
  if (x == null)
    return n;
  else
  {
    n = n + 1;
    return size_helper(x.next, n);
  }
}

// The number of nodes in a doubly linked list
int size(node2 x)
  requires x::dll<_>
  ensures true;
{
  int n = 0;
  return size_helper(x, n);
}

// Get the first element in the doubly linked list.
int front(node2 x)
  requires x::node2<v,_,q> * q::dll<x> 
  ensures res=v;
{
  return x.val;
}

void swap(ref node2 x, ref node2 y)
  requires x::dll<p> * y::dll<q>
  ensures x'::dll<q> * y'::dll<p>;
{
  node2 tmp = x;
  x = y;
  y = tmp;
}

// Erase current content and add n elements with the same value v
void assign(ref node2 x, int n, int v)
  requires x::dll<_>
  ensures x'::dll<_>;
{
  x = create_list(n, v);
}

void push_front(ref node2 x, int v)
  requires x::dll<p>
  ensures x'::node2<v,_,q> * q::dll<x'>;
{
  node2 tmp = new node2(v,null,x);
  if (x!=null){
    tmp.prev = x.prev;
    x.prev = tmp;
  }
  x = tmp;
}

// Get rhe first node
node2 pop_front(ref node2 x)
  requires x::node2<v,p,q> * q::dll<x>
  ensures x'::dll<null> * res::node2<v,p,null> & x'=q;
{
  node2 tmp = x;
  if (x.next == null)
  {
    x = x.next;
    tmp.next=null;
    return tmp;
  }
  else
  {
    x.next.prev = null;
    x = x.next;
    tmp.next = null;
    return tmp;
  }
}

/* Append a doubly linked list */
void append(node2 x, node2 y)
  requires x::dll<p> * y::dll<q> & x!=null
  ensures x::dll<p>;
{
  if (x.next == null)
  {
    x.next = y;
    if (y != null)
    {
      y.prev = x;
    }
  }
  else
  {
    append(x.next, y);
  }
}

/* Get the head of a doubly linked list */
node2 ret_first(node2 x)
  requires x::dll<p>
  ensures x::dll<p>;
{
  return x;
}

/* Get the tail of a doubly linked list */
node2 get_next(node2 x)
  requires x::node2<v,_,q> * q::dll<x> 
  ensures x::node2<v,null,null> * res::dll<null> & res=q;
{
  node2 tmp = x.next;
  if (tmp!=null)
    tmp.prev = null;
  x.prev = null;
  x.next = null;
  return tmp;
}

/* Set the tail of a list */
void set_next(node2 x, node2 y)
  requires x::dll<p> * y::dll<_> & x!=null
  ensures x::node2<_,p,null> or x::node2<_,p,y> * y::dll<x>;
{
  if (y==null) 
    x.next = y;
  else
  {
    x.next = y;
    y.prev = x;
  }
}

/* Set the tail to be null */
void set_null(node2 x)
  requires x::dll<p> & x!=null
  ensures x::node2<_,p,null>;
{
  x.next = null;
}

/* Set the tail to be null */
void set_null2(node2 x)
  requires x::dll<p> & x!=null
  ensures x::node2<_,p,null>;
{
  if (4>3){
    x.next = null;
  }
  else {
    x.next = null;
  }
}

/* Get the third node of a doubly linked list */
node2 get_next_next(node2 x)
  requires x::node2<_,_,p1> * p1::node2<_,x,p2> * p2::dll<p1>
  ensures res::dll<p1> & res=p2;
{
  return x.next.next;
}

/* Insert "a" into a non-null doubly linked list */
void insert(node2 x, int a)
  requires x::dll<p> & x!=null
  ensures x::dll<p>;
{
  if (x.next == null){
    node2 tmp = new node2(a, null, null);
    x.next = tmp;
    tmp.prev = x;
  }
  else
    insert(x.next, a);
}


/* Delete the i_th node in a doubly linked list */
void del_index(node2 x, int i)
  requires x::dll<p> & x!=null
  ensures x::dll<p>;
{
  if (i == 1)
  {
    if (x.next.next != null){
      node2 tmp = x.next;
      x.next.next.prev = x;
      x.next = x.next.next;
      free(tmp);
    }
    else{
      x.next = null;
    }
  }
  else
  {
    del_index(x.next, i-1);
  }
}

/* Delete the node with value a */
node2 del_val(node2 x, int a)
  requires x::dll<_>
  ensures res::dll<_>;
{
  if (x == null)
    return x;
  else
  {
    if (x.val == a)
    {
      node2 tmp = x.next;
      if (tmp!=null){
        tmp.prev = x.prev;
        free(x);
        return tmp; 
      }
      else
        return null;
    }
    else
    {
      node2 r = del_val(x.next,a);
      x.next = r;
      if (r!=null)
        r.prev = x;
      return x;
    }
  }
}

/* Create a doubly linked list */
node2 create_list(int n, int v)
  requires true 
  ensures res::dll<_>;
{
  if (n == 0)
  {
    return null;
  }
  else
  {
    n  = n - 1;
    node2 tmp = create_list(n, v);
    if (tmp == null)
      return new node2 (v,null,null);
    else {
      node2 tmp2 = new node2 (v, null, tmp);
      tmp.prev = tmp2;
      return tmp2;
    }
  }
}

/* Reverse a doubly linked list */
void reverse(ref node2 xs, ref node2 ys)
  requires xs::dll<_> * ys::dll<_>
  ensures ys'::dll<_> & xs'=null;
{
  if (xs != null)
  {
    node2 tmp;
    tmp = xs.next;
    xs.next = ys;
    if (ys!=null)
      ys.prev = xs;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

/* Split a doubly linked list into two:
   the first part contains "a" nodes
*/
node2 del_lseg(node2 x, int a)
  requires x::dll<p>
  ensures x::dll<p> * res::dll<null>;
{
  node2 tmp;
  if (a == 1)
  {
    tmp = x.next; 
    x.next = null;
    tmp.prev = null;
    return tmp;
  }
  else
  {
    a = a - 1;
    bind x to (_, xprev, xnext) in
    {
      tmp = del_lseg(xnext, a);
    }
    return tmp;
  }
}

/********* SMALLFOOT EXAMPLES *************/

/* Traverse a doubly linked list */
void traverse(node2 x)
  requires x::dll<p>
  ensures x::dll<p>;
{
  node2 t;
  if (x != null) {
    t = x;
    traverse(x.next);
  }
}

/* Copy a doubly linked list */
node2 copy(node2 x)
  requires x::dll<p>
  ensures x::dll<p> * res::dll<null>;
{
  node2 tmp;
  if (x != null) {
    tmp = copy(x.next);
    node2 tmp2 = new node2 (x.val, null, tmp);
    if (tmp==null)
      return tmp2;
    else {
      tmp.prev = tmp2;
      return tmp2;
    }
  }
  else
    return null;
}


/* Remove the first node which has value v */
void list_remove(node2 x, int v)
  requires x::dll<p> & x!=null
  ensures x::dll<p>;
{
  if(x.next != null) {
    if(x.next.val == v) {
      node2 tmp = x.next;
      if (x.next.next!=null)
        x.next.next.prev = x;
      x.next = x.next.next;
      free(tmp);
    }
    else {
      list_remove(x.next, v);
    }
  }
}

/* Remove the first node which has value v 
   in a nullable doubly linked list
*/
node2 list_remove2(node2 x, int v)
  requires x::dll<_>
  ensures res::dll<_> ;
{
  node2 tmp;
  if(x != null) {
    if(x.val == v) {
      tmp = x;
      if (x.next!=null)
        x.next.prev = x.prev;
      x = x.next;
      free(tmp);
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

/* Remove all nodes which have value v 
   in nullable doubly linked list
*/
node2 list_filter(node2 x, int v)
  requires x::dll<_>
  ensures res::dll<_>;
{
  node2 tmp;
  if(x != null) {
    if(x.val == v){
      tmp = x.next;
      free(x);
      x = tmp;
      x = list_filter(x,v);
    }
    else{
      tmp = list_filter(x.next, v);
      if (tmp!=null)
        tmp.prev = x;
      x.next = tmp;
    }
  }
  return x;
}

/******** SLAYER EXAMPLES **********/

/* Get the first node greater than v */
node2 find_ge(node2 x, int v)
  requires x::dll<_>
  ensures res = null or res::node2<m,_,_> & m>v;
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

/* Splice 2 doubly linked list */
void splice (ref node2 x, node2 y)
  requires x::dll<p> * y::dll<_>
  ensures x'::dll<_>;
{
  if(x == null)
    x = y;
  else {
    if (y != null){
      node2 nx = x.next;
      node2 ny = y.next;
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
