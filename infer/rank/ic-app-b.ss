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

!!! REL INFERRED:[RELASS [R]: ( 0<=m & 0<=flted_7_579 & 0<=flted_7_579 & 0<=m & flted_7_579+1=n & 
flted_7_579=flted_7_579 & m=m & l1=l1 & s2=s2 & l2=l2 & s2<=l2 & 
s1_581<=l1 & s1_581<=l1 & s1_581=s1_581 & q_580=q_580 & flted_15_662=m+
flted_7_579 & q_580!=null & q_580!=null & l1=l1 & s2<=l2 & s1<=s1_581 & 
(q_580=null & flted_15_662=0 & s3_663<=l2 | q_580!=null & s3_663<=l2 & 
1<=flted_15_662) & R(s3_663,l3_664,s1_581,l1,s2,l2) & s1=s1 & s3_663=s3_663) -->  s1<=s3_663]

!!! REL INFERRED:[RELASS [R]: ( 0<=m & 0<=flted_7_579 & 0<=flted_7_579 & 0<=m & flted_7_579+1=n & s2<=l2 & 
s1_581<=l1 & s1_581<=l1 & flted_15_662=m+flted_7_579 & q_580!=null & 
q_580!=null & s2<=l2 & s1<=s1_581 & (q_580=null & flted_15_662=0 & 
s3_663<=l2 | q_580!=null & s3_663<=l2 & 1<=flted_15_662) & 
R(s3_663,l3_664,s1_581,l1,s2,l2)) -->  s1<=s3_663]



!!! REL INFERRED:[RELASS [R]: ( 
0<=m & 0<=flted_7_579 & flted_7_579+1=n &  
s1_581<=l1 & flted_15_662=m+flted_7_579 
& q_580!=null & s2<=l2 & s1<=s1_581 & 
(q_580=null & flted_15_662=0 & s3_663<=l2 | q_580!=null & s3_663<=l2 & 
1<=flted_15_662) & 
R(s3_663,l3_664,s1_581,l1,s2,l2) ) -->  s1<=s3_663]

!!! REL INFERRED:
[RELASS [R]: ( 0<=m & 0<=n_595 & 0<=flted_7_579 & s2<=l2 & 0<=m & flted_7_579+1=n & 
l1=l1 & q_580!=null & q_580!=null & n_595=flted_7_579 & m=m & flted_15_662=m+
n_595 & q_666=q_580 & s1<=s1_581 & s1_596=s1_581 & s1_581<=l1 & s1_596<=l1 & 
s2<=l2 & (q_580=null & flted_15_662=0 & s3_663<=l2 | q_580!=null & 
s3_663<=l2 & 1<=flted_15_662) & l2=l2 & s2=s2 & l1=l1 & 
R(s3_663,l3_664,s1_596,l1,s2,l2) & s1=s1 & s1_667=s3_663) -->  s_577<=s1_667]
!

!!! REL INFERRED:[RELDEFN R: ( s2<=l2 & s3=s1 & l1<=s2 & exists(s1_581:s1<=s1_581 & s1_581<=l1)) -->  R(s3,l3_625,s1,l1,s2,l2)]
!!! alias:[(l_578,l1),(n_595,flted_7_579),(m_598,m),(q_666,q_580),(s1_596,s1_581),(l2_600,l2),(s2_599,s2),(l1_597,l_578),(s_577,s1),(s1_667,s3_663)]
!!! rest:[(s1_667,s3_663),(s1_596,s1_581),(q_666,q_580),(n_595,flted_7_579)]
!!! subs:[(s_577,s1),(l1_597,l_578),(s2_599,s2),(l2_600,l2),(m_598,m),(l_578,l1)]
!!! nsubs:[(s_577,s1),(l1_597,l1),(s2_599,s2),(l2_600,l2),(m_598,m),(l_578,l1)]
!!
!!! alias:
[(l_578,l1),(n_595,flted_7_579),(m_598,m),(q_666,q_580),(s1_596,s1_581),(l2_600,l2),(s2_599,s2),(l1_597,l_578),(s_577,s1),(s1_667,s3_663)]

!!! subs:[(s_577,s1),(l1_597,l_578),(s2_599,s2),(l2_600,l2),(m_598,m),(l_578,l1)]
!!! nsubs:
[(s_577,s1),(l1_597,l1),(s2_599,s2),(l2_600,l2),(m_598,m),(l_578,l1)]

!!! REL INFERRED:[RELASS [R]: 
( 0<=m & 0<=n_595 & 0<=flted_7_579 & s2<=l2 & 0<=m & flted_7_579+1=n & 
l1=l1 & q_580!=null & q_580!=null & n_595=flted_7_579 & m=m & flted_15_662=m+
n_595 & q_666=q_580 & s1<=s1_581 & s1_596=s1_581 & s1_581<=l1 & s1_596<=l1 & 
s2<=l2 & (q_580=null & flted_15_662=0 & s3_663<=l2 | q_580!=null & 
s3_663<=l2 & 1<=flted_15_662) & l2=l2 & s2=s2 & l1=l1 & 
R(s3_663,l3_664,s1_596,l1,s2,l2) & s1=s1 & s1_667=s3_663) -->  s_577<=s1_667]
:
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

