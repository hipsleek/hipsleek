data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

int length(node x)
  requires x::ls<null,n>
  ensures x::ls<null,n> & res = n;
{
  if (x == null) return 0;
  else {
    int k;
    k = 1 + length(x.next);
    return k;
  }
}

node delete_first(node x)
  requires x::ls<null,n> & n<=1 ensures res=null;
  requires x::node<a,t> * t::ls<null,n> ensures t::ls<null,n> & res=t;
{
  if (x == null)
    return null;
  else if (x.next == null) {
    free(x);
    return null;
  }
  else {
    node y = x.next;
    free(x);
    return y;
  }
}

node delete_last(node x)
  requires x::ls<null,n> & n<=1 ensures res=null;
  requires x::ls<null,n> & n>1 ensures x::ls<null,n-1>;
{
  if (x == null)
    return null;
  else if (x.next == null) {
    free(x);
    return null;
  }
  else if (x.next.next == null)  {
    free(x.next);
    x.next = null;
    return x;
  }
  else {
    delete_last(x.next);
    return x;
  }
}

node insert_first(node x , int a)
  requires x::ls<null,n>
  ensures res::ls<null,n+1>;
{
  node u = new node(a, null);
  u.next = x;
  return u;
}

node insert_first2(node x , int a)
  requires x::ls<null,n>
  ensures res::node<a,x> * x::ls<null,n>;
{
  node u = new node(a, null);
  u.next = x;
  return u;
}

node insert_last(node x , int a)
  requires x::ls<null,n> & n=0 ensures res::ls<null,1>;
  requires x::ls<null,n> & n>0 ensures x::ls<null,n+1> & res=x;
{
  if (x == null) {
    node u = new node(a, null);
    return u;
  }
  else if (x.next == null) {
    node u = new node(a, null);
    x.next = u;
    return x;
  }
  else {
    insert_last(x.next, a);
    return x;
  }
}

node insert_last2(node x , int a)
  requires x::ls<null,n> & n=0 ensures res::node<a,null>;
  requires x::ls<null,n> & n>0 ensures x::ls<y,n> * y::node<a,null> & res=x;
{
  if (x == null) {
    node u = new node(a, null);
    return u;
  }
  else if (x.next == null) {
    node u = new node(a, null);
    x.next = u;
    return x;
  }
  else {
    insert_last2(x.next, a);
    return x;
  }
}

node concat(node x, node y)
  requires x::ls<null,n> * y::ls<null,m> & n=0
    ensures res::ls<null,m> & res=y;
  requires x::ls<null,n> * y::ls<null,m> & n>0
    ensures res::ls<null,n+m> & res=x;
{
  if (x == null)
    return y;
  else if (x.next == null) {
    x.next = y;
    return x;
  }
  else {
    concat(x.next, y);
    return x;
  }
}

void main () {
  node x = new node(10, null);
  node y = new node(11, null);
  node z = new node(12, null);
  x.next = y;
  y.next = z;
  z.next = null;

  // dprint;

  // int n = length(x);
  // dprint;
  // assert (n' = 3);

  // dprint;
  // node t = delete_first(x);
  // dprint;
  // int m = length(t);
  // dprint;
  // assert (m' = 2);

  // node u = delete_first(t);
  // int l = length(u);
  // assert (l' = 1);
}
