/* selection sort */

data node {
	int val; 
	node next; 
}

llMM<mi> == self::node<v,null> & mi=v  
  or self::node<v, p> * p::llMM<mi2> & mi=min(v,mi2) 
  //& v<=mi2
inv self!=null;

relation P1(int a1, int a2).
relation P2(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3).

node sel(ref node x)
     infer [P1,P2]
     requires x::llMM<mi> 
     ensures  res::node<m,_> & x'=null & P1(m,mi2)
           or res::node<m,_> * x'::llMM<mi2> & P2(m,mi,mi2)
     ;
/*
[RELDEFN P1: ( true) -->  P1(m,mi2),
RELDEFN P1: ( P1(m_646,mi2_647) & m=m_646) -->  P1(m,mi2),
RELDEFN P2: ( P1(m_646,mi2_647) & m=m_646 & mi<=mi2 & m_646<=mi2) -->  P2(m,mi,mi2),
RELDEFN P1: ( P2(m_653,mi_621,mi2_654) & m=m_653) -->  P1(m,mi2),
RELDEFN P2: ( P2(m_653,mi_621,mi2_654) & ((mi=mi2 & m=m_653 & m<=mi & mi<=(mi2_654-1) & 
mi<=(mi_621-1)) | (mi=mi_621 & m=m_653 & mi<=mi2 & m<=mi2 & mi2<mi2_654) | 
(mi2=mi2_654 & m=m_653 & m<=mi & mi2_654<=mi & mi<mi_621) | (mi=mi_621 & 
mi2=mi2_654 & m=m_653))) -->  P2(m,mi,mi2),
RELDEFN P1: ( P1(m_646,mi2_647) & m<m_646) -->  P1(m,mi2),
RELDEFN P2: ( P1(m_646,mi2_647) & m_646=mi2 & mi<=m & m<mi2) -->  P2(m,mi,mi2),
RELDEFN P1: ( P2(m_653,mi_621,mi2_654) & m<m_653) -->  P1(m,mi2),
RELDEFN P2: ( P2(m_653,mi_621,mi2_654) & ((m=mi & m_653=mi2 & mi<mi2 & mi2<mi2_654 & 

[( P2(m,mi,mi2), false, true, true),
( P1(m,mi2), false, true, true)]
*************************************

!!! REL POST :  P1(m,mi2)
!!! POST:  false
!!! REL PRE :  true
!!! PRE :  false
!!! REL POST :  P2(m,mi,mi2)
!!! POST:  false
!!! REL PRE :  true
!!! PRE :  false
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

