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
  inv self!=null;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;

int assignChar(str x,int v)
  requires x::str<_,q> & Term[]
  ensures x::str<v,q>;


void while2(ref str s1,ref str s2)
  requires s1::str<_,q>*q::BADS<> * s2::WFS<p>@L 
  ensures s1::WFSeg<s1a>*s1a::str<0,s1'>*s1'::BADS<> & s1'=ppp;
{
  int x=getChar(s2);
  assignChar(s1,x);
  s2 = incStr(s2);
  s1 = incStr(s1);
  if (x!=0) {
    while2(s1,s2);
  }
}

/*
# ex12f.ss

2nd Loop verifies but we need to use unbounded BADS<> for shape-only
verification

*/
