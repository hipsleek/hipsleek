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


/*
hecking procedure insert$node~node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R2: ( b<=v2_668) -->  R2(b,v2_668),
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

*************************************

*/
