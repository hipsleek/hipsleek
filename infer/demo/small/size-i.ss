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

/******************************************/

/* Append a singly linked list */
relation P1(int a, int b).
relation Q1(int a, int b, int c).


void append(node x, node y)
/*  infer {ll->llN} []*/
/*  requires x::ll<> * y::ll<> & x!=null*/
/*  ensures x::ll<>;*/
  infer [P1,Q1]
  requires x::llN<n> * y::llN<m> & x!=null & P1(n,m)
  ensures x::llN<z> & Q1(n,m,z);
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/* Copy a singly linked list */
relation P2(int a).
relation Q2(int a, int b).

node copy(node x)
  infer [P2,Q2]
  requires x::llN<n> & P2(n)
  ensures x::llN<m> & Q2(n,m);
{
  node tmp;
  if (x != null) {
    tmp = copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

void free(ref node x)
  requires x::node<_,_>
  ensures x'=null;

/* Delete the i_th node in a singly linked list */
/* Similar to zip example, 
   this example need size property
   to ensure the memory safety.
*/
void del_index(node x, int i)
  infer [P1,Q1]
  requires x::llN<n> & P1(i,n)
  ensures x::llN<m> & Q1(n,m,i);
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
  infer [P1,Q1]
  requires x::llN<n> & P1(n,a)
  ensures res::llN<m> & Q1(n,m,a);
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
  infer [P2,Q2]
  requires x::llN<n> & x!=null & P2(n)
  ensures x::llN<m> & Q2(n,m);
{
  if (x.next == null)
    x.next = new node(a, null);
  else
    insert(x.next, a);
}

/* Traverse a singly linked list */
void traverse(node x)
  infer [P2,Q2]
  requires x::llN<n> & P2(n)
  ensures x::llN<m> & Q2(n,m);
{
  node t;
  if (x != null) {
    t = x;
    traverse(x.next);
  }
}
