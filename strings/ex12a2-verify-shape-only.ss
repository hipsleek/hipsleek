
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
  or self::str<v,q>*q::WFSeg<p> & v>0
  inv true;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;
 
void while1(ref str s)
/*
  requires s::WFS<p> 
  ensures s::WFSeg<s'>*s'::str<0,p>;
*/
  requires s::WFS<p> 
  ensures s::WFSeg<ss>*ss::str<0,p> & ss=s';
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
# ex12a2.ss

Why isn't ss implicit?

   exists (Expl)[](Impl)[p](ex)[]s::WFS<p>@M&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       ref [s]
       (exists p_62,flted_31_61,
       ss: s::WFSeg<ss>@M * ss::str<flted_31_61,p_62>@M&
       flted_31_61=0 & ss=s' & p_62=p&{FLOW,(4,5)=__norm#E}[]


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
