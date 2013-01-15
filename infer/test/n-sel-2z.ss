
/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<v,mi,mx> == self::node<v,null> & mi=v  & mx=v
  or self::node<v, p> * p::llMM<v2,mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2)
  //& v<=mi2
inv self!=null & mi<=v<=mx;

relation P3(int v,int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3,int a5,int a6).
relation P7(int b, int a,int a1, int a2,int a3,int a5,int a6).

node sel(ref node x)
     //infer [P3,P4,P5]
     infer [P3,P7]
     requires x::llMM<v1,mi,mx> 
     ensures  res::node<m,_> & x'=null & P3(v1,m,mi,mx)
           or res::node<m,_> * x'::llMM<v2,mi2,mx2> 
                    //& P4(m,mi,mi2) & P5(m,mx,mx2)
                    & P7(v1,v2,m,mi,mi2,mx,mx2)
     ;
/*
## n-sel-2a.ss

*************************************
[( P4(m,mi,mi2), m=mi & m<=mi2, true, true),
( P5(m,mx,mx2), mx=mx2 & m<=mx, true, true),
( P3(m,mi,mx), m=mi & m=mx, true, true)]
*
*************************************

!!! REL POST :  P3(m,mi,mx)
!!! POST:  m=mi & mi<=mx
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P5(m,mx,mx2)
!!! POST:  m<=mx2 & mx2<=mx
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P4(m,mi,mi2)
!!! POST:  m=mi & mi<=mi2
!!! REL PRE :  true
!!! PRE :  true
P

*/
{
  node tmp;
  if (x.next==null)
    { tmp=x; x=null; return tmp;}
  else {
    tmp = x.next;
    node n = sel(tmp);
    if (n.val<=x.val) {
       x.next = tmp;
       return n;
    } else {
      node r = x;
      n.next = tmp;
      x = n;
      return r;
    }
  }
}

