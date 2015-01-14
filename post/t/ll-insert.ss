data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

void insert(node x, int a)
  infer [@post_n]
  requires x::ll<n> & n>0
  ensures x::ll<r>;
{
  if (x.next == null) {
    x.next = new node(a,null);
  } else {
    insert(x.next,a);
  }
}

void insert2(node x, int a)
  infer [@pre_n,@post_n]
  requires x::ll<n>
  ensures x::ll<r>;
{
  if (x.next == null) {
    x.next = new node(a,null);
  } else {
    insert(x.next,a);
  }
}
