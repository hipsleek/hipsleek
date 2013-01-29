/* Size Property */
data node {
  int val;
  node next;
}

ll<> == self = null
  or self::node<_, q> * q::ll<>
  inv true;

llN<n> == self = null & n=0
  or self::node<_, q> * q::llN<n-1>
  inv n>=0;

void append(node x, node y)
  infer {ll->llN} []
  requires x::ll<> * y::ll<> & x!=null
  ensures x::ll<>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

node copy(node x)
  infer {ll->llN} []
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

void del_index(node x, int i)
  infer {ll->llN} []
  requires x::ll<>
  ensures x::ll<>;
{
  if (i == 1)
  {
    x.next = x.next.next;
  }
  else
  {
    del_index(x.next, i-1);
  }
}

void free(node x)
  requires true
  ensures true;

node del_val(node x, int a)
  infer {ll->llN} []
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

void insert(node x, int a)
  infer {ll->llN} []
  requires x::ll<> & x!=null
  ensures x::ll<>;
{
  if (x.next == null)
    x.next = new node(a, null);
  else
    insert(x.next, a);
}

void traverse(node x)
  infer {ll->llN} []
  requires x::ll<>
  ensures x::ll<>;
{
  node t;
  if(x != null) {
    t = x;
    traverse(x.next);
  }
}
