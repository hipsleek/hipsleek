data node {
	int val;
	node next;
}


ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

relation P(int a, int b).


void append3(node x, node y)
  infer [P]
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null & P(l1,s2) 
  ensures x::ll3<n+m,s1,l2> ;
{
   if (x.next==null) {
     x.next=y;
   } else {
      append3(x.next,y);
   }
}


