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

node insert(node x, node y)
     infer [R]
     requires x::sortHO<a,R> * y::node<v,null>
     ensures  res::sortHO<b,R> & (v>a & b=v | (a>=v & b=a));
     // ensures  res::sortHO<b,R> & (v>a & b=a | (a>=b & b=v));
/*

[RELDEFN R: ( b<=v2_668) -->  R(b,v2_668),
RELDEFN R: ( a=v2_706 & v2_616=v2_724 & R(a,v2_616)) -->  R(v2_706,v2_724),
RELDEFN R: ( v2_706=v_614 & a=v2_706 & v2_616=v2_724 & b<=v2_706 & R(a,v2_616) & 
R(v_614,v2_724)) -->  R(b,v2_706),
RELDEFN R: ( b<v2_749) -->  R(b,v2_749),
RELDEFN R: ( ((a=b & a<v2_789 & v2_789<=v2_616) | (a=b & v2_616=v2_789)) & R(a,v2_616)) -->  R(b,v2_789)]

*************************************
*******fixcalc of pure relation *******
*************************************
[( R(b,v2_668), v2_668>=b, true, true)]
*************************************

!!! REL POST :  R(b,v2_668)
!!! POST:  v2_668>=b
!!! REL PRE :  true
!!! PRE :  true

*/
{
    if (y.val>=x.val) {
        y.next = x; return y;
    } else {
      if (x.next==null) x.next=y;
      else {
        x.next = insert(x.next,y);
      };
      return x;
    }
}

