/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi,mx> == self::node<v,null> & mi=v & mx=v 
  or self::node<v, p> * p::llMM<mi2,mx2> 
     & mi=min(v,mi2) & mx=max(v,mx2)
inv self!=null;


relation R(int a1, int a2,int a3).
relation P(int a1, int a2,int a3,int a4, int a5).
relation P1(int a1, int a2,int a3).
relation P2(int a1, int a2,int a3).

node insert(node x, node y)
     infer [P1,P2]
     requires x::llMM<mi,mx> * y::node<a,null> 
      //& R(a,mi,mx)
     ensures  res::llMM<mi2,mx2> & P1(mi,a,mi2) & P2(mx,a,mx2);
/*
!!! REL POST :  P2(mx,a,mx2)
!!! POST:  (mx=mx2 & a<=mx) | (a=mx2 & mx<mx2)
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P1(mi,a,mi2)
!!! POST:  (a=mi2 & a<=mi) | (mi=mi2 & mi2<=a)
!!! REL PRE :  true
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

