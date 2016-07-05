data node {
	int val;
	node next;
}

ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

relation R(int s3, int l3, int s2, int l2, int s1, int l1).
//relation R(int s3, int s2, int s1).
 
void append3(node x, node y)
  infer [R]//,s1,l2
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null & l1<=s2
  ensures x::ll3<n+m,s3,l3> & R(s3,l3,s2,l2,s1,l1)   ;
{
   if (x.next==null) {
     //assume false;
     x.next=y;
   } else {
      append3(x.next,y);
   }
}


