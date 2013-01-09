/* selection sort */

data node {
	int val; 
	node next; 
}

// needs infinity
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
     ensures  res::sortHO<b,R2> & (v>a & b=a | (a>=b & b=v));
/*

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R2: ( b<=v2_671) -->  R2(b,v2_671),
RELDEFN R2: ( R(a,v2_619) & R(r_744,a_745)) -->  R2(r_744,a_745),
RELDEFN R2: ( a=v2_709 & v2_619=v2_727 & R(a,v2_619) & R(r_744,a_745)) -->  R2(v2_709,v2_727),
RELDEFN R2: ( v2_709=v_617 & a=v2_709 & v2_619=v2_727 & b<=v2_709 & R(a,v2_619) & 
R(r_744,a_745) & R2(v_617,v2_727)) -->  R2(b,v2_709),
RELDEFN R2: ( b<v2_758) -->  R2(b,v2_758),
RELDEFN R2: ( ((a=b & a<v2_798 & v2_798<=v2_619) | (a=b & v2_619=v2_798)) & R(a,v2_619)) -->  R2(b,v2_798)]
*************************************

Context of Verification Failure: File "n-ins-3c.ss",Line:26,Col:14
Last Proving Location: File "n-ins-3c.ss",Line:43,Col:8
ERROR: at _0_0 
Message: unify_rels: Expected a relation
!!! PROBLEM with fix-point calculation
Procedure insert$node~node FAIL-2
Exception Failure("unify_rels: Expected a relation") Occurred!
Error(s) detected when checking procedure insert$node~node

PROBLEM
=======

The above triggers FIX-POINT computation but
had an error. I wonder if mutual-recursive
fixpoint is the cause of problem. It may be
good to print more information prior to
the FIXPOINT process, so we can tell 
what causes such problems.

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

