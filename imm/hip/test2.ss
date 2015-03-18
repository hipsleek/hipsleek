data node{
 int val;
 node next;
}

ls<p> == self=p or
  self::node<_,q>*q::ls<p> //& self!=p
  inv true;

//SUCCESS
node push(node u, int x)
  requires u::ls<p>
  ensures  q::node<x,u> * u::ls<p> & res=q ;
{
  node tmp;
  tmp = new node(x,null);
  if (u == null) return tmp;
 else {
    tmp.next = u;
    u = tmp;
    return u;
  }
}

//SUCCESS
node iterator(node b)
  requires b::ls<p>@L
  ensures  res=b;
{
  return b;
}

//SUCCESS
void foo(node s)
  requires s::ls<null>
  ensures  s::ls<null>;
{
  int v;
}

//SUCCESS
void foo_lend(node s)
  requires s::ls<null>@L
  ensures  emp;
{
  int v;
}

//SUCCESS
void goo_lend(int x, int y, int z, node s)
{
  assume s::ls<null>;
  node i1, i2, tmp;
  s = push(s,x);
  i1 = iterator(s);
  s = push(s,y);
  i2 = iterator(s);
  s = push(s,z);
  foo_lend(s);
  i2 = i2.next;
  assert i1' = i2';
}

//FAIL
void goo(int x, int y, int z, node s)
{
  assume s::ls<null>;
  node i1, i2, tmp;
  s = push(s,x);
  i1 = iterator(s);
  s = push(s,y);
  i2 = iterator(s);
  s = push(s,z);
  foo(s);
  i2 = i2.next;
  assert i1' = i2';
}
