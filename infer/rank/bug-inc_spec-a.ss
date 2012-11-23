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
    r = x.next;
    r = append1(r,y);
    node d = x.next;
	if (d==null) {
      x.next = r;
	}
    else {
      // no guarantee that x.next=r here!
      assume false;
    }
    return x;
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

