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
     infer [P]
     requires x::llMM<mi,mx> * y::node<a,null> 
      //& R(a,mi,mx)
     ensures  res::llMM<mi2,mx2> & P(mi,a,mi2,mx,mx2);
/*
*************************************
*******fixcalc of pure relation *******
*************************************
[( P(mi,mx,a,mi2,mx2), (mi=mi2 & mx<=mx2 & a<=mx2 & (mi+mx2)<=(mx+a)) | (mx=mx2 & a=mi2 & 
mi2<=mi & mi<=mx), true, true)]
*************************************

!!! REL POST :  P(mi,mx,a,mi2,mx2)
!!! POST:  (mi=mi2 & mx<=mx2 & a<=mx2 & (mi+mx2)<=(mx+a)) | (mx=mx2 & a=mi2 & 
mi2<=mi & mi<=mx)
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

