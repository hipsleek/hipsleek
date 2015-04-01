data node{
 int val;
 node next;
}

ls<p,a,b> == self=p or
  self::node<_@a,q@b>*q::ls<p,a,b> //& self!=p
  inv true;


//SUCCESS
node push(node u, int x)
  requires u::ls<p,@A,@A>
  ensures  q::node<x,u>  & res=q ;
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
  requires b::ls<p,@A,@L>
  ensures  res=b;
{
  return b;
}

//SUCCESS
void foo(node s)
  requires s::ls<null,@M,@M>
  ensures  s::ls<null,@M,@M>;
{
  int v;
}

//SUCCESS
void foo_lend(node s)
  requires s::ls<null,@M,@L>
  ensures  s::ls<null,@M,@A>;
{
  int v;
}


//SUCCESS
void goo_lend(int x, int y, int z, node s)
{
  assume s::ls<null,@M,@M>;
  node i1, i2, tmp;
  // dprint;
  s = push(s,x);
  i1 = iterator(s);
  s = push(s,y);
  i2 = iterator(s);
  s = push(s,z);
  //  dprint;
  foo_lend(s);
  //  dprint;
  i2 = i2.next;
  dprint;
  assert i1' = i2';
}


//FAIL
void goo(int x, int y, int z, node s)
{
  assume s::ls<null,@M,@M>;
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

