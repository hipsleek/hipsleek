data node{
 int val;
 node next;
}

ll<n> == self=null & n=0 or
  self::node<_,q>*q::ll<n-1>
  inv n>=0;

ls<n,p> == self=p & n=0 or
  self::node<_,q>*q::ls<n-1,p> & self!=p
  inv n>=0;

void append(node x, node y)
  requires x::ll<n> * y::ll<m> & x!=null
  ensures  x::ll<c> & c=n+m;
{
  if (x.next == null)  x.next = y;
  else append(x.next,y);
  //  dprint;
}

void append2(node x, node y)
  requires x::ls<n,q> * q::node<_,null> * y::ls<m,null>
  ensures  x::ls<n,q> * q::node<_,y> * y::ls<m,null>;
{
  if (x.next == null)  x.next = y;
  else   append2(x.next,y);
}

int length(node x)
  requires x::ls<n,null>@L
  ensures  res=n;
{
  if (x==null) return 0;
  else 
    { assume x::node<_,_>@L;
      node tmp = x.next;
      return 1 + length(tmp);
    }
}

int length2(node x)
  requires x::ls<n,null>
  ensures  x::ls<n,null> & res=n;
{
  if (x==null) return 0;
  else 
    { assume x::node<_,_>@L;
      node tmp = x.next;
      return 1 + length2(tmp);
    }
}

void foo(node y)
  requires y::ls<m,_> 
  ensures  y::ls<m,_>;
{
  if (y != null) { assume y::node<_,_>; y.val = 0;}
}

void main()
{
  node x,y;
  x = new node(10,null);
  y = new node(20,null);
  dprint;
  append2(x,y);
  //dprint;
  int n = length(x);
  foo(y);
  dprint;
}

void main2()
{
  node x,y;
  x = new node(10,null);
  //dprint;
  y = new node(20,null);
  //dprint;
  append2(x,y);
  //dprint;
  int n = length2(x);
  //dprint;
  foo(y);
  dprint;
}
