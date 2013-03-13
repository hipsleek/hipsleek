/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<v,mi,mx> == self::node<v,null> & mi=v & mx=v 
  or self::node<v, p> * p::llMM<_,mi2,mx2> 
     & mi=min(v,mi2) & mx=max(v,mx2)
inv self!=null & mi<=v<=mx;

relation R(int a1, int a2,int a3).
relation P3(int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).

node insert(node x, node y)
     infer [R,P3,P4,P5]
     requires x::llMM<v,mi,mx> * y::node<a,null> & R(a,mi,mx)
     ensures  res::llMM<v2,mi2,mx2> 
         & P3(mi,a,mi2) 
         & P4(mx,a,mx2)
         & P5(v2,v,a)
     ;
/*
P5 indicates that sorting is based on an ascending technique

!!! REL POST :  P5(v2,v,a)
!!! POST:  (a=v2 & a<=v) | (v=v2 & v2<a)
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P4(mx,a,mx2)
!!! POST:  (mx=mx2 & a<=mx) | (a=mx2 & mx<mx2)
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P3(mi,a,mi2)
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

