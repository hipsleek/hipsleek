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
  infer [R]
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & R(a,v,b);
//b,a,v);

/*
//  requires x::sortA<a> * y::node<v,null>
//  ensures  res::sortA<b> & (v>=(1+a) | (a>=b & b=v)) ;


  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & (b=a | (a>=b & b=v)) ;

!!! REL :  R(b,a,v)
!!! POST:  v>=(1+a) | (a>=b & b=v)
!!! PRE :  true

[
[RELDEFN R: ( b=v & b<=a) -->  R(b,a,v),
RELDEFN R: ( b=v & b<=a) -->  R(b,a,v),
RELDEFN R: ( a=b & b<v) -->  R(b,a,v),
RELASS [R]: ( R(b_658,a_642,v_643)) -->  (a_642<=b_658 & b_658<=(v_643-2)) | v_643<=(b_658+1),
RELDEFN R: ( a=b & v=v_643 & b<=b_658 & b<=(v-1) & b<=a_642 & R(b_658,a_642,v_643)) -->  R(b,a,v)]
// why isn't disj obligation captured?

*************************************
*******fixcalc of pure relation *******
*************************************
[( R(b,a,v), (a>=b & b=v) | (v>=(1+b) & a=b))]
*************************************

!!! REL :  R(b,a,v)
!!! POST:  (a>=b & b=v) | (v>=(1+b) & a=b)
!!! PRE :  true

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










