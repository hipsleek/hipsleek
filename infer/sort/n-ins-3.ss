/* selection sort */

data node {
	int val; 
	node next; 
}

// needs infinity
sortA<v> == self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 
inv self!=null;

relation R(int r, int a, int b).

node insert(node x, node y)

  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & (v>a & b=a | (a>=b & b=v)) ;

/*
  infer [R]
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & R(a,v,b);

  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & (v>a & b=a | (a>=b & b=v)) ;

Checking procedure insert$node~node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R: ( b=v & b<=a) -->  R(a,v,b),
RELDEFN R: ( b=v & b<=a) -->  R(a,v,b),
RELDEFN R: ( a=b & b<v) -->  R(a,v,b),
RELASS [R]: ( R(a_642,v_643,b_658)) -->  (a_642<=b_658 & b_658<=(v_643-2)) | v_643<=(b_658+1),
RELDEFN R: ( a=b & v=v_643 & b<=b_658 & b<=(v-1) & b<=a_642 & R(a_642,v_643,b_658)) -->  R(a,v,b)]

*************************************
*******fixcalc of pure relation *******
*************************************
[( R(a,v,b), (a>=b & b=v) | (v>=(1+b) & a=b))]
*************************************

!!! REL :  R(a,v,b)
!!! POST:  (a>=b & b=v) | (v>=(1+b) & a=b)
!!! PRE :  true
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










