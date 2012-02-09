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

void append1(node x, node y)
  requires x::ll1<>*y::ll1<> & x!=null 
  ensures x::ll1<>; 
  requires x::ll2<n>*y::ll2<m> & n>0
  ensures x::ll2<n+m>;
{
   if (x.next==null) {
     x.next=y;
   } else {
      append1(x.next,y);
   }
}

void append2(node x, node y)
  infer [A,rk]
  requires x::ll2<n>*y::ll2<m> & Term[rk(n)] & x!=null
  ensures x::ll2<t> & A(t,m,n);
{
   if (x.next==null) {
     x.next=y;
   } else {
      append2(x.next,y);
   }
}


