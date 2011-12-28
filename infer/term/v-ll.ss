data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int length(node x)
  requires x::ll<n>@L
  variance (0,p) [n]
  ensures res=n;
{
  if (x==null) return 0;
  else {
    int m = length(x.next);
    return 1+m;
  }
}


int foo(node x)
  requires x::ll<n>@L
  variance (0,q) [n]
  ensures res=0;
{
  if (x==null) return 0;
  else {
    int m = foo(x.next);
    return m;
  }
}


void append(node x, node y)
  requires x::ll<n>*y::ll<m> & n>0
  variance [0,0,n]
  ensures x::ll<n+m>;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}




