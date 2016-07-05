
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
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3,int a5,int a6).

node sel(ref node x)
     //infer [P3,P4,P5]
     infer [P3,P6]
     requires x::llMM<mi,mx> 
     ensures  res::node<m,_> & x'=null & P3(mi,mx,m)
           or res::node<m,_> * x'::llMM<mi2,mx2> 
                    //& P4(m,mi,mi2) & P5(m,mx,mx2)
                    & P6(m,mi,mi2,mx,mx2)
                    //& P6(mi,mx,m,mi2,mx2)
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
!!! POST:  m=mi & m=mx
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P6(m,mi,mi2,mx,mx2)
!!! POST:  m=mi & mx=mx2 & m<=mi2 & mi2<=mx
!!! REL PRE :  true
!!! PRE :  true

[RELDEFN P3: ( m=mx & mi=mx) -->  P3(m,mi,mx),
RELDEFN P6: ( P3(m,mi,mx_636) & mi2=mx & mi2=mx2 & mi<=mx_636 & mx_636<=mi2 & m<=mi2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P3(m,mi,mx) & mi2=mx2 & mi<=mi2 & m<=mi2 & mi2<mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P3(m,mi_635,mx) & mi=mi2 & mi2=mx2 & m<=mi2 & mi2<mi_635 & mi_635<=mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2<=mx2_669 & P6(m,mi,mi2,mx_636,mx2_669) & mx=mx2 & mi<=mx_636 & 
mx_636<=mx & mx2_669<=mx & m<=mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2<=mx2_669 & P6(m,mi,mi2,mx,mx2_669) & mx2_669<=mx2 & mi<=mx2 & m<=mx2 & 
mx2<mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2<=mx2_669 & P6(m,mi_635,mi2,mx,mx2_669) & mi=mx2 & mx2_669<=mi & m<=mi & 
mi<mi_635 & mi_635<=mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P6(m,mi,mi2,mx_636,mx2) & mi2<=mx & m<=mx & mx_636<=mx & mx<mx2 & mi<=mx_636) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2<=(mx2-1) & P6(m,mi,mi2,mx,mx2) & mi<=(mx2-1) & mi<=(mx-1) & mi2<=(mx-
1) & m<=(mx2-1) & m<=(mx-1)) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P6(m,mi_635,mi2,mx,mx2) & m<=mi & mi2<=mi & mi<mi_635 & mi_635<=mx & mi<mx2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2_668<=mx2 & P6(m,mi,mi2_668,mx_636,mx2) & mi2=mx & m<=mx & mx_636<=mx & 
mx<mi2_668 & mi<=mx_636) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2_668<=mx2 & P6(m,mi,mi2_668,mx,mx2) & mi<=mi2 & m<=mi2 & mi2<mi2_668 & 
mi2<mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2_668<=mx2 & P6(m,mi_635,mi2_668,mx,mx2) & mi=mi2 & m<=mi & mi<mi2_668 & 
mi<mi_635 & mi_635<=mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P3(mi2,mi,mx_636) & m=mx & mi2=mx2 & mi<=mx_636 & mx_636<=mx & mx<mi2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P3(mi2,mi,mx) & mi2=mx2 & mi<=m & m<=(mx-1) & m<=(mi2-1)) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( P3(mi2,mi_635,mx) & m=mi & mi2=mx2 & mi<mi_635 & mi_635<=mx & mi<mi2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mx2_669<=mx2 & mi2<=mx2_669 & P6(mx2,mi,mi2,mx_636,mx2_669) & m=mx & 
mi<=mx_636 & mx_636<=mx & mx<mx2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mx2_669<=mx2 & mi2<=mx2_669 & P6(mx2,mi,mi2,mx,mx2_669) & mi<=m & m<=(mx-
1) & m<=(mx2-1)) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mx2_669<=mx2 & mi2<=mx2_669 & P6(mx2,mi_635,mi2,mx,mx2_669) & m=mi & 
mi<mi_635 & mi_635<=mx & mi<mx2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2<=m_667 & m_667<mx2 & P6(m_667,mi,mi2,mx_636,mx2) & m=mx & mi<=mx_636 & 
mx_636<=mx & mx<m_667) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2<=m_667 & m_667<mx2 & P6(m_667,mi,mi2,mx,mx2) & mi<=m & m<m_667 & m<mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( m_667<mx2 & mi2<=m_667 & P6(m_667,mi_635,mi2,mx,mx2) & m=mi & (mi+
1)<=m_667 & mi<mi_635 & mi_635<=mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2_668<=mx2 & mi2<mi2_668 & P6(mi2,mi,mi2_668,mx_636,mx2) & m=mx & 
mi<=mx_636 & mx_636<=mx & mx<mi2) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2_668<=mx2 & mi2<mi2_668 & P6(mi2,mi,mi2_668,mx,mx2) & mi<=m & m<mi2 & 
m<mx) -->  P6(m,mi,mi2,mx,mx2),
RELDEFN P6: ( mi2_668<=mx2 & mi2<mi2_668 & P6(mi2,mi_635,mi2_668,mx,mx2) & m=mi & 
mi<mi2 & mi<mi_635 & mi_635<=mx) -->  P6(m,mi,mi2,mx,mx2)]

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

