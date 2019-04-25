data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2
  inv n>=0;

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

node delete_first2(node x)
  requires x::ls<null,n> & n<=1 ensures res=null;
  requires x::ls<null,n> & n>1 ensures res::ls<null,n-1>;
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
  requires x::ls<null,n> & n>1 ensures x::ls<null,n-1> & res=x;
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

node get_last(node x)
  requires x=null ensures res=null;
  requires x::ls<y,n> * y::node<a,null>
    ensures x::ls<y,n> * y::node<a,null> & res=y;
{
  if (x == null)
    return null;
  else if (x.next == null)
    return x;
  else
    return get_last(x.next);
}

node delete_all(node x)
  requires x::ls<null,n> ensures emp & res=null;
{
  if (x == null)
    return null;
  else {
    node t = x.next;
    free(x);
    delete_all(t);
    return null;
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
  requires x::ls<null,n> * y::ls<null,m> & x!=null
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

node reverse(node x)
  requires x=null ensures res=null;
  requires x::ls<null,n> & x!=null ensures res::ls<null,n> & res!=null;
{
  if (x == null)
    return x;
  else if (x.next == null)
    return x;
  else {
    node u = x.next;
    x.next = null;
    node y = reverse(u);
    node z = concat(y, x);
    return z;
  }
}

node main1 ()
  requires true
  ensures res::ls<y,n> * y::node<a,null>;
{
  node x1 = new node(1, null);
  node x2 = new node(1, x1);
  node x3 = new node(1, x2);
  node x4 = new node(1, x3);
  node x5 = new node(1, x4);
  node x6 = new node(1, x5);
  node x7 = new node(1, x6);
  node x8 = new node(1, x7);
  int n = length(x8);
  return x8;
}

node main2 (node x, node y)
  requires x::ls<null,10>
  ensures x::ls<u,9> * u::node<_,null> & res=u;
{
  node u = get_last(x);
  return u;
}

node main3 (node x, node y)
  requires x::ls<y,n> * y::node<1,z> & n>2
  ensures res::ls<z,n+1> & x=res;
{
  return x;
}
