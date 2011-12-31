data node {
  int val;
  node next;
}

logical int p1, p2, p3;

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

// note that p1,p2,p3 are global
int length(node x)
  //infer @pre [p1]
  requires x::ll<n>@L
  variance [p1,0,n]
	//variance [0,p1]{n}
  ensures res=n;
{
  if (x==null) return 0;
  else {
    int m = length(x.next);
    return 1+m;
  }
}

int foo(node x)
  // infer @pre [p1,p2,p3]
  requires x::ll<n>@L
  //variance [0,p2,n]
	variance [0,0,n]
  ensures res=0;
{
  if (x==null) return 0;
  else {
    int m = foo(x.next);
    return m;
  }
}

void append(node x, node y)
  // infer @pre [p1,p2,p3]
  requires x::ll<n>*y::ll<m> & n>0
  //variance [0,p3]{n}
	variance [0,0,n]
  ensures x::ll<n+m>;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}




