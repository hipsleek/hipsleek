
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
  or self::str<v,q>*q::WFSeg<p> & v>1
  inv true;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;
 
void while1(ref str s)
  requires s::WFS<p> 
  ensures s::WFSeg<s'>*s'::str<0,p>;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
# ex12a.ss

seems to be a proving bug

  v!=0 |= v>0 
 
WFS<p> ==
  self::str<0,p>
  or self::str<v,q>*q::WFS<p> & v!=0 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::str<v,q>*q::WFSeg<p> & v>0
  inv true;


*/
