/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi,mx> == self::node<v,null> & mi=v  & mx=v
  or self::node<v, p> * p::llMM<mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2)
  //& v<=mi2
inv self!=null & mi<=mx;

relation P3(int a1, int a2,int a3).
relation P4(int m, int mi,int mi2, int mx,int mx2)
 == (m=mi & m<=mx2 & mi2<=mx2 & mx2<=mx & m<mx) 
               | (m=mi & m<=mi2 & mi2<=mx2 & mx2<=mx) .
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3).

node sel(ref node x)
     infer [P3]
     requires x::llMM<mi,mx> 
     ensures  res::node<m,_> & x'=null & P3(m,mi,mx)
           or res::node<m,_> * x'::llMM<mi2,mx2> 
                    & P4(m,mi,mi2,mx,mx2)
     ;
/*


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


!!! REL POST :  P3(m,mi,mx)
!!! POST:  m=mi & mi<=mx
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P4(m,mi,mi2,mx,mx2)
!!! POST:  (m=mi & m<=mx2 & mi2<=mx2 & mx2<=mx & m<mx) 
               | (m=mi & m<=mi2 & mi2<=mx2 & mx2<=mx)
!!! REL PRE :  true
!!! PRE :  true
Procedure sel$node SUCCESS


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

