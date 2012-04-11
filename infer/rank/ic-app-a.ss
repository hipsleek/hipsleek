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

ll3<n,s,l> == self=null & n=0 & s=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

ranking rk(int a, int b).

relation A(int a, int b, int c).
relation P(int a, int b).

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

void append3(node x, node y)
  //infer [l1,s2]//,s1,l2]
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null & l1<=s2
     //& s1<=s2 
     //& l1<=s2
  ensures x::ll3<n+m,s3,_> & s1<=s3  ; // why not derive this?& l3<=l2; 
{
   if (x.next==null) {
     //assume false;
     x.next=y;
   } else {
      append3(x.next,y);
   }
}


