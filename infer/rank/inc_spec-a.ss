data node {
	int val;
	node next;
}

ll1<> == self=null 
	or self::node<_, q> * q::ll1<>
	inv true;

ll2<n> == self=null & n=0
	or self::node<_, q> * q::ll2<n-1>
	inv n>=0;


ranking rk(int a, int b).

relation A(int a, int b, int c).

node append1(node x, node y)
  requires x::ll1<>*y::ll1<> 
  ensures res::ll1<>;
{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append1(r,y);
     x.next = r;
     return x;
    }
}

node append2(node x, node y)
  requires x::ll2<n>*y::ll2<m> 
  ensures res::ll2<n+m>;
{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append2(r,y);
     x.next = r;
     return x;
    }
}

node append3(node x, node y)
  infer [A,rk]
  requires x::ll2<n>*y::ll2<m> & Term[rk(n)]
  ensures res::ll2<t> & A(t,m,n);
{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append3(r,y);
     x.next = r;
     return x;
    }
}

/*
node append4(node x, node y)
  infer [A,rk] 
  requires x::ll2<n>*y::ll2<m> & Term[rk(n)]
  ensures res::ll2<t> & A(t,m,n);
{
    node r;
	if (x==null) return y;
    r = x.next;
    r = append4(r,y);
	if (x.next==null) {
      x.next = r;
	}
    return x;
}
*/

