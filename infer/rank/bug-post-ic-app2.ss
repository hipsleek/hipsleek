data node {
	int val;
	node next;
}

ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

/*
WHY did this fixpoint gave a problem?
Checking procedure append3$node~node... 
!!! IGNORING PROBLEM of fix-point calculation
!!! NEW RELS:[ (s3=s1 & s1<=s2) --> R(s3,s2,s1),
 (s3=s1 & s2_595=s2 & s1<=s1_592 & s1_592<=s2 & s1_592<=s3_656 & 
  R(s3_656,s2_595,s1_592)) --> R(s3,s2,s1)]
  !
*/

//relation R(int s3, int l3, int s2, int l2, int s1, int l1).
relation R(int s3, int s2, int s1).
 
void append3(node x, node y)
  infer [R]//,s1,l2
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null & l1<=s2
  ensures x::ll3<n+m,s3,l2> & R(s3,s2,s1)   ;
{
   if (x.next==null) {
     //assume false;
     x.next=y;
   } else {
      append3(x.next,y);
   }
}


