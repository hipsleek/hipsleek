/* Size Property */
data node {
  int val;
  node next;
}

ll<> == self = null
  or self::node<_, q> * q::ll<>;

/******************************************/

/* Append a singly linked list */
void append(node x, node y)
  requires x::ll<> * y::ll<> & x!=null
  ensures x::ll<>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* Copy a singly linked list */
node copy(node x)
  requires x::ll<>
  ensures x::ll<> * res::ll<>;
{
  node tmp;
  if (x != null) {
    tmp = copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

void free(node x)
  requires x::node<_,_>
  ensures x=null;

/* Delete the i_th node in a singly linked list */
/* Similar to zip example, 
   this example need size property
   to ensure the memory safety.
*/
void del_index(node x, int i)
  requires x::ll<>
  ensures x::ll<>;
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
  requires x::ll<>
  ensures res::ll<>;
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

/* Insert "a" into a non-null singly linked list */
void insert(node x, int a)
  requires x::ll<> & x!=null
  ensures x::ll<>;
{
  if (x.next == null)
    x.next = new node(a, null);
  else
    insert(x.next, a);
}

/* Traverse a singly linked list */
void traverse(node x)
  requires x::ll<>
  ensures x::ll<>;
{
  node t;
  if (x != null) {
    t = x;
    traverse(x.next);
  }
}
