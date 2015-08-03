
data str {
  int val;
  str next;
}

WFS<p> ==
  self::str<0,p> 
  or self::str<v,q>*q::WFS<p> & v!=0 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::str<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::str<v,q>*q::BADS<> 
  inv true;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;

void assignStr(str x,int v)
  requires x::str<_,q> & Term[]
  ensures  x::str<v,q> ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
relation PP(str s, str a, str b, str c).
void while1(ref str s)
  infer [PP]
  requires s::WFS<p> 
  ensures (exists a,b: s::WFSeg<a>*a::str<0,b> & PP(a,p,s',b)) ;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
# ex10a1.ss

  infer [PP]
  requires s::WFS<p> 
  ensures (exists a,b: s::WFSeg<a>*a::str<0,b> & PP(a,p,s',b)) ;

Inferred:

!!! **pi.ml#775:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#776:>>REL POST:  PP(p,a_68,s',b_69)
!!! **pi.ml#777:>>POST:  a_68!=null & a_68=s' & p=b_69
!!! **pi.ml#778:>>REL PRE :  true
!!! **pi.ml#779:>>PRE :  true

Can we tidy name printing to use a,b instead?

*/
