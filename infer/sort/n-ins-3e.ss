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
     ensures  res::sortHO<b,R2> 
        &  b=min(a,v) 
        //& (v>a & b=a | (a>=b & b=v))
     ;
/*
Without the post-relation b=min(a,v), how come
we are able to infer sortedness property below.
Have we checked the obligations?

How come we still can have strongest post for R2?
I suppose the last defn ( R(b,v2_615)) -->  R2(b,v2_794)
cannot be proven.

[RELDEFN R2: ( b<=v2_667) -->  R2(b,v2_667),
RELDEFN R2: ( R(r_740,a_741)) -->  R2(r_740,a_741),
RELDEFN R2: ( R(v2_705,v2_723)) -->  R2(v2_705,v2_723),
RELDEFN R2: ( R2(v2_705,v2_723) & R(v2_705,v2_723) & b<=v2_705) -->  R2(b,v2_705),
RELDEFN R2: ( b<v2_754) -->  R2(b,v2_754),
RELDEFN R2: ( R(b,v2_615)) -->  R2(b,v2_794)]

Below is the currect version.


RELDEFN R2: ( b<=v2_668) -->  R2(b,v2_668),
RELDEFN R2: ( R(r_741,a_742)) -->  R2(r_741,a_742),
RELDEFN R2: ( R(v2_706,v2_724)) -->  R2(v2_706,v2_724),
RELDEFN R2: ( R2(v2_706,v2_724) & R(v2_706,v2_724) & b<=v2_706) -->  R2(b,v2_706),
RELDEFN R2: ( b<v2_755) -->  R2(b,v2_755),
RELDEFN R2: ( R(b,v2_616) & b<v2_795 & v2_795<=v2_616) -->  R2(b,v2_795),
RELDEFN R2: ( R(b,v2_795)) -->  R2(b,v2_795)]

*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R2(b,v2_668), b<=v2_668, R(r_741,a_742), r_741<=a_742)]
*************************************

!!! REL POST :  R2(b,v2_668)
!!! POST:  b<=v2_668
!!! REL PRE :  R(r_741,a_742)
!!! PRE :  r_741<=a_742
Procedure insert$node~node SUCCESS


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

