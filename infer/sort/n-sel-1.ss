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
     ensures  res::node<m,_> & x'=null & P1(m,mi)
           or res::node<m,_> * x'::llMM<mi2> & P2(m,mi,mi2)
     ;
/*
[RELDEFN P1: ( m=mi) -->  P1(m,mi),
RELDEFN P1: ( P1(m_642,mi_620) & ((m=m_642 & m<=mi & mi<mi_620) | (mi=mi_620 & m=m_642))) -->  P1(m,mi),
RELDEFN P2: ( P1(m_642,mi_620) & ((m=m_642 & mi=mi2 & m<=mi & mi<mi_620) | (mi=mi_620 & 
m=m_642 & mi<=mi2 & m<=mi2))) -->  P2(m,mi,mi2),
RELDEFN P1: ( P2(m_648,mi_620,mi2_649) & ((m=m_648 & m<=mi & mi<mi_620) | (mi=mi_620 & 
m=m_648))) -->  P1(m,mi),
RELDEFN P2: ( P2(m_648,mi_620,mi2_649) & ((mi=mi2 & m=m_648 & m<=mi & mi<=(mi2_649-1) & 
mi<=(mi_620-1)) | (mi=mi_620 & m=m_648 & mi<=mi2 & m<=mi2 & mi2<mi2_649) | 
(mi2=mi2_649 & m=m_648 & m<=mi & mi2_649<=mi & mi<mi_620) | (mi=mi_620 & 
mi2=mi2_649 & m=m_648))) -->  P2(m,mi,mi2),
RELDEFN P1: ( P1(m_642,mi_620) & ((m=mi & mi<=(m_642-1) & mi<=(mi_620-1)) | (mi=mi_620 & 
mi<=m & m<m_642))) -->  P1(m,mi),
RELDEFN P2: ( P1(m_642,mi_620) & ((m=mi & m_642=mi2 & mi<=(mi_620-1) & mi<=(m_642-1)) | 
(mi=mi_620 & m_642=mi2 & mi<=m & m<m_642))) -->  P2(m,mi,mi2),
RELDEFN P1: ( P2(m_648,mi_620,mi2_649) & ((m=mi & mi<=(m_648-1) & mi<=(mi_620-1)) | 
(mi=mi_620 & mi<=m & m<m_648))) -->  P1(m,mi),
RELDEFN P2: ( P2(m_648,mi_620,mi2_649) & ((m=mi & m_648=mi2 & mi<mi2 & mi2<mi2_649 & 
mi<mi_620) | (mi=mi_620 & m_648=mi2 & mi<=m & m<mi2 & mi2<mi2_649) | (m=mi & 
mi2=mi2_649 & mi<=(mi_620-1) & mi<=(m_648-1) & mi2_649<=m_648) | 
(mi=mi_620 & mi2=mi2_649 & mi<=m & m<m_648 & mi2_649<=m_648))) -->  P2(m,mi,mi2)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( P2(m,mi,mi2), m=mi & mi<=mi2, true, true),
( P1(m,mi), m=mi, true, true)]
*************************************

!!! REL POST :  P1(m,mi)
!!! POST:  m=mi
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  P2(m,mi,mi2)
!!! POST:  m=mi & mi<=mi2
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

