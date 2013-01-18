/* insertion algorithm */

data node {
	int val; 
	node next; 
}

/*
sortA<v> == self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 
inv self!=null;
*/

sortHO<v,R:relation(int,int)> == 
  self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) 
inv self!=null;

relation R(int r, int a).
relation R2(int r, int a).

node insert(node x, node y)

     infer [R,R2]
     requires x::sortHO<a,R> * y::node<v,null>
     ensures  res::sortHO<b,R2> &  b=min(a,v)
    ;
/*
     requires x::sortA<a> * y::node<v,null>
     ensures  res::sortA<b,> &  b=min(a,v) 
        //& (v>a & b=a | (a>=b & b=v))
     ;
*/
/*
!!! REL POST :  R2(b,v2_671)
!!! POST:  b<=v2_671
!!! REL PRE :  R(r_744,a_745)
!!! PRE :  r_744<=a_745
P

[RELDEFN R2: ( b<=v2_671) -->  R2(b,v2_671),
RELDEFN R2: ( R(a,v2_619) & R(r_744,a_745)) -->  R2(r_744,a_745),
RELDEFN R2: ( R(r_744,a_745) & R(a,v2_619) & a=v2_709 & v2_619=v2_727) 
    -->  R2(v2_709,v2_727),
RELDEFN R2: ( v2_619=v2_727 & R2(v_617,v2_727) & R(r_744,a_745) & R(a,v2_619) & 
v2_709=v_617 & a=v2_709 & b<=v2_709) -->  R2(b,v2_709),
RELDEFN R2: ( b<v2_758) -->  R2(b,v2_758),
RELDEFN R2: ( R(a,v2_619) & ((a=b & a<v2_798 & v2_798<=v2_619) | (a=b & v2_619=v2_798))) -->  R2(b,v2_798)]
*************************************


PROBLEM
=======

We need a stronger post-condition.

Algorithm
=========
(i) For each 
     X & Pre(..) --> Post(...)
    determine if X -> Post(..) reduces to true --> Post(...)
    and remove it if so, for pre-condition obligation later
(ii) Form a definition for Post(..) to compute least fix-point.
(iii) Extract pre from Post and form an assumption
          Pre(..) -> Y_i
(iv) For each obligation of form:
       X & Pre(..) --> ..
     determine relational assumptions of the form:
       Pre(..) --> Y_j
(v) Form an initial Precondition
      Pre(..) -> Y wher Y=Y1 & ... & Yn
   Check if current pre satisfies all the obligation
      ... & Pre(..) --> Pre(..)
(vi) If not, perform a top-down fix-point using 
      ... & Pre(..) --> Pre(..)
    to ensure it satisfies 
      Pre(..) --> Y
    for all recursive invocations.

 Can we obtain the following specs:
  requires x::sortHO<a,R0> & R0(a,b)-->a<=b // cond on R0
  ensures  res::sortHO<b,R1> & b<=a & R2(a,b)-->a<=b;
  requires x::sortHO<a,R0> // no condition on R0(..)
  ensures  res::sortHO<b,R1> & b<=a &
    b<=v2_671 -->  R2(b,v2_671),
    R(v2_709,v2_627) -->  R2(v2_709,v2_727)
    R(v2_709,v2_727) &  b<=v2_709 -->  R2(b,v2_709)
    R(b,v2_619) & b<v2_798 & v2_798<=v2_619 -->  R2(b,v2_798)]

*/
{
    if (y.val<=x.val) {
        y.next = x; return y;
    } else {
      if (x.next==null) x.next=y;
      else {
        x.next = insert(x.next,y);
      };
      return x;
    }
}

