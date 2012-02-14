data node {
	int val;
	node next;
}

ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

relation R(int s3, int l3, int s2, int l2, int s1, int l1).
 
void append3(node x, node y)
  infer [R,l1,s2]
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null
  ensures x::ll3<n+m,s3,l2> & R(s3,l3,s1,l1,s2,l2)   ;
{
   if (x.next==null) {
     //assume false;
     x.next=y;
   } else {
      append3(x.next,y);
   }
}
/*

!!! NEW ASSUME:[ 

(0<=m_599 & 0<=n_596 & 0<=flted_7_580 & s2<=l2 & 0<=m & flted_7_580+1=n & 
  l_579=l1 & l1<=s2 & q_581!=null & q_581!=null & n_596=flted_7_580 & 
  m_599=m & flted_15_663=m_599+n_596 & q_667=q_581 & s1<=s1_582 & 
  s1_597=s1_582 & s1_582<=l_579 & s1_597<=l1_598 & s2_600<=l2_601 & 
  (q_581=null & flted_15_663=0 & s3_664<=l2_601 | q_581!=null & 
  s3_664<=l2_601 & 1<=flted_15_663) & l2_601=l2 & s2_600=s2 & l1_598=l_579 & 
  R(s3_664,l3_665,s1_597,l1_598,s2_600,l2_601) & s_578=s1 & 
  s1_668=s3_664) --> s_578<=s1_668]

// maybe can simplify..

(0<=m_599 & 0<=n_596 & 0<=flted_7_580 & s2<=l2 & 0<=m & flted_7_580+1=n & 
  l1<=s2 & q_581!=null & q_581!=null & n_596=flted_7_580 & 
  m_599=m & flted_15_663=m_599+n_596 & q_667=q_581 & s1<=s1_582 & 
  s1_582<=l1 & s2_600<=l2 & 
  (q_581=null & flted_15_663=0 & s3_664<=l2 | q_581!=null & 
  1<=flted_15_663)  & s2_600=s2  & 
  R(s3_664,l3_665,s1_582,l1,s2_600,l2_601) ) --> s1<=s3_664]


*/

