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
  /*

   existential wrap s3,l3 causes problem?

   !!! curr vars:[n,s1,l1,m,s2,l2,x,y]
!!! fv post:[x,m,n,R,s1,l1,s2,l2]
!
   */

{
   if (x.next==null) {
     //assume false;
     x.next=y;
   } else {
      append3(x.next,y);
   }
}
/*

 P(s2,l1) -> l1<=s2


- duplicates
- null=null
- under disj
- use CP.simplify_disj_new 

!!! NEW ASSUME:[ 

!! REL INFERRED:[RELASS [P,R]: 


RELDEFN P: ( P(s2,l1) & s2=s2_601 & l1_599=l1 & exists(l2:exists(s1_583:s2_601<=l2 & 
exists(s1:s1_583<=l1 & s1<=s1_583)))) -->  P(s2_601,l1_599)]

 (flted_7_581+1=n & null=null & null=null & 
  (null=null & flted_7_581=0 & 
  s1_583<=l1 | null!=null & s1_583<=l1 & 1<=flted_7_581)
   & s1<=s1_583 & s1_583<=l1 
  (y=null & m=0 & s2<=l2 | y!=null & s2<=l2 & 1<=m) 
  & P(s2,l1)
  ) 
   --> s1<=s2,
 

( s2<=l2 & s1_583<=l1 & s1_583<=l1 & s2<=l2 & P(s2,l1) & s1<=s1_583 & 
s3_667<=l2 & R(s3_667,l3_668,s1_583,l1,s2,l2)) -->  s1<=s3_667,

 (0<=m & 0<=flted_7_581 & 0<=flted_7_581 & 0<=m & flted_7_581+1=n & s2<=l2 & 
  s1_583<=l1 & s1_583<=l1 & flted_16_666=m+flted_7_581 & q_582!=null & 
  q_582!=null & s2<=l2 & 
  P(s2,l1) 
  & s1<=s1_583 & (q_582=null & 
  flted_16_666=0 & s3_667<=l2 | q_582!=null & s3_667<=l2 & 
  1<=flted_16_666) 
  & R(s3_667,l3_668,s1_583,l1,s2,l2)) // s3_667=s1
    s1_593<=l1

  s1<=l1 & l1<=s2 & s2<=l2 
   --> s1<=s3_667]

RELDEFNS
========

P(s2,l1) & s2<=l2 & s3=s1 & l1<=s2 & exists(s1_583:s1<=s1_583 & 
  s1_583<=l1)) --> R(s3,l3_628,s1,l1,s2,l2)

,
 (l1_599=l1 & s2_601=s2 & s3=s1 & l2_602=l2 & s3_667<=l2 & s2<=l2 & 
  P(s2,l1) & R(s3_667,l3_668,s1_598,l1_599,s2_601,l2_602) & s1_598<=s3_667 & 
  s1<=s1_598 & s1_598<=l1) --> R(s3,l3_669,s1,l1,s2,l2)

,
 (P(s2,l1) & s2=s2_601 & l1_599=l1 & exists(l2:exists(s1_583:s2_601<=l2 & 
  exists(s1:s1_583<=l1 & s1<=s1_583)))) --> P(s2_601,l1_599)]

REL ASSUME
==========

(flted_7_581+1=n &  (null=null & flted_7_581=0 & 
  s1_583<=l1 | null!=null & s1_583<=l1 & 1<=flted_7_581) & s1<=s1_583 & 
  (y=null & m=0 & s2<=l2 | y!=null & s2<=l2 & 1<=m) & P(s2,l1)) 
    --> s1<=s2

,
 (0<=m & 0<=flted_7_581 & 0<=flted_7_581 & 0<=m & flted_7_581+1=n & s2<=l2 & 
  s1_583<=l1 & s1_583<=l1 & flted_16_666=m+flted_7_581 & q_582!=null & 
  q_582!=null & s2<=l2 & P(s2,l1) & s1<=s1_583 & (q_582=null & 
  flted_16_666=0 & s3_667<=l2 | q_582!=null & s3_667<=l2 & 
  1<=flted_16_666) & 
  R(s3_667,l3_668,s1_583,l1,s2,l2)) 
   --> s1<=s3_667]


  s1<=s1
 */
