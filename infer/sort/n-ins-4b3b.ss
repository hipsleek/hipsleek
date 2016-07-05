/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<v,mi,mx> == self::node<v,null> & mi=v & mx=v 
  or self::node<v, p> * p::llMM<_,mi2,mx2> 
     & mi=min(v,mi2) & mx=max(v,mx2)
inv self!=null;

relation P3(int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).

node insert(node x, node y)
     infer [P3,P4,P5]
     requires x::llMM<v,mi,mx> * y::node<a,null> 
      //& R(a,mi,mx)
     ensures  res::llMM<v2,mi2,mx2> 
         & P3(mi,a,mi2) 
         & P4(mx,a,mx2)
         & P5(v2,v,a)
     ;
/*

PROBLEM : some time-outs and very large RELDEFN. 
 see a-ins-4b3a.ss.
 It is important to do the simplification mechanisms
 for RELDEFN.

Checking procedure insert$node~node... Timeout when checking #simplify  Restarting Omega after ... 166 invocations Stop Omega... 166 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 167 invocations Stop Omega... 167 invocations Starting Omega...oc

!!! REL POST :  P4(mx,a,mx2)
!!! POST:  (mx=mx2 & a<=mx) | (a=mx2 & mx<mx2)
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P3(mi,a,mi2)
!!! POST:  (a=mi2 & a<=mi) | (mi=mi2 & mi2<=a)
!!! REL PRE :  true
!!! PRE :  true
Total verification time: 15.200949 second(s)
	Time spent in main process: 6.4044 second(s)
	Time spent in child processes: 8.796549 second(s)

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

