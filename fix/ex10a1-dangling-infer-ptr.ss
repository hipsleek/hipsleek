
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
relation PPP(str s, str a, str b, str c).
void while1(ref str s)
  infer [PPP]
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<0,b> & PPP(a,p,s',b) ;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
    //dprint;
  }
}

/*
# ex10a1.ss

 infer [PPP]
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<0,b> & PPP(a,p,s',b) ;

GOT
===
!!! **infer.ml#2210:RelInferred (simplified):[RELDEFN PPP: ( a!=null & PPP(a,p,s',b)) -->  PPP(a,p,s',b)]
!!! **infer.ml#2210:RelInferred (simplified):[RELDEFN PPP: ( b=p & a=s' & s'!=null) -->  PPP(a,p,s',b)]


Expects
=======
  s'=a  & b=p

GOT a better result:

!!! **pi.ml#776:>>REL POST:  PPP(p,a,s',b)
!!! **pi.ml#777:>>POST:  a!=null & a=s' & p=b


*/
