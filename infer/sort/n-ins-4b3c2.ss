/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<v,mi> == self::node<v,null> & mi=v  
  or self::node<v, p> * p::llMM<_,mi2> & mi=min(v,mi2) 
  //& v<=mi2
inv self!=null;

relation P3(int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3).

node insert(node x, node y)
     infer [P6]
     requires x::llMM<v,mi> * y::node<a,null> 
      //& R(a,mi,mx)
     ensures  res::llMM<v2,mi2> 
        & v2=min(v,a) & P6(mi,a,mi2)
     ;
/*

!!! REL POST :  P6(mi,a,mi2)
!!! POST:  (a=mi2 & a<=mi) | (mi=mi2 & mi2<=a)
!!! REL PRE :  true
!!! PRE :  true

Algo for sortedness
 (i) check if min/max preserving
 (ii) check if head is decreasing or increasing
 (iii) check if sorted specialization can be used

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

