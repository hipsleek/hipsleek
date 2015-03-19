data node{
 int val;
 node next;
}


ls<n,p> == self=p & n=0 or
  self::node<_,q>*q::ls<n-1,p> & self!=p
  inv n>=0;

void concat(node x, node y)
  requires x::ls<n,q> * q::node<_,null> * y::ls<m,null>
  ensures  x::ls<n,q> * q::node<_,y> * y::ls<m,null>;
{
  if (x.next == null)  x.next = y;
  else   concat(x.next,y);
}

int length_lend(node x)
  requires x::ls<n,null>@L
  ensures  res=n;
{
  if (x==null) return 0;
  else 
    { assume x::node<_,_>@L;
      node tmp = x.next;
      return 1 + length_lend(tmp);
    }
}

int length(node x)
  requires x::ls<n,null>
  ensures  x::ls<n,null> & res=n;
{
  if (x==null) return 0;
  else 
    { assume x::node<_,_>@L;
      node tmp = x.next;
      return 1 + length(tmp);
    }
}

void foo(node y)
  requires y::ls<m,null> 
  ensures  y::ls<m,null>;
{
  if (y != null) { assume y::node<_,_>; y.val = 0;}
}

void main_lend()
{
  node x,y;
  x = new node(10,null);
  y = new node(20,null);
  //  dprint;
  concat(x,y);
  int n = length_lend(x);
  foo(y);
  // dprint;
}

void main()
{
  node x,y;
  x = new node(10,null);
  y = new node(20,null);
  concat(x,y);
  int n = length(x);
  foo(y);
  //  dprint;
}
