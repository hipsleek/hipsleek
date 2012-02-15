data node {
	int val;
	node next;
}

ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

relation R(int s3, int l3, int s2, int l2, int s1, int l1).
relation P(int s2, int l1).
 
void append3(node x, node y)
  infer [R,P]
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null & P(s2,l1)
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
   (flted_7_581+1=n & q_582=null & q_582=null & q_629=y & s1<=s1_583 & 
  (q_582=null & flted_7_581=0 & s1_583<=l1 | q_582!=null & 
  s1_583<=l1 & 1<=flted_7_581) & (y=null & m=0 & s2<=l2 | y!=null & 
  s2<=l2 & 1<=m) & l_580=l1 
  & P(s2,l1) ) --> s1<=s2,
 (

   P(s2,l1) & 0<=m_600 & 0<=n_597 & 0<=flted_7_581 & s2<=l2 & 0<=m & 
  flted_7_581+1=n & l_580=l1 & q_582!=null & q_582!=null & 
  n_597=flted_7_581 & m_600=m & flted_16_666=m_600+n_597 & q_670=q_582 & 
  s1<=s1_583 & s1_598=s1_583 & s1_583<=l_580 & s1_598<=l1_599 & 
  s2_601<=l2_602 & (q_582=null & flted_16_666=0 & s3_667<=l2_602 | 
  q_582!=null & s3_667<=l2_602 & 1<=flted_16_666) & l2_602=l2 & s2_601=s2 & 
  l1_599=l_580 & R(s3_667,l3_668,s1_598,l1_599,s2_601,l2_602) & s_579=s1 & 
  s1_671=s3_667) --> s_579<=s1_671]


 (P(s2,l1) & s2=s2_601 & l1_599=l1 & exists(l2:exists(s1_583:s2_601<=l2 & 
  exists(s1:s1_583<=l1 & s1<=s1_583)))) --> P(s2_601,l1_599)]


 */
