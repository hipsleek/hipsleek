/*
data str {
  int val;
  str next;
}
*/

WFS<> ==
  self::char_star<0,q>*q::BADS<> 
  or self::char_star<v,q>*q::WFS<> & v>0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v>0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> & v>=0
  inv true;

void while1(ref char_star s)
  requires s::WFS<> 
  ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;
{
  int x=__get_char(s);
  if (x!=0) {
    // dprint;
    s = __plus_plus_char(s);
    //dprint;
    while1(s);
  }
}
