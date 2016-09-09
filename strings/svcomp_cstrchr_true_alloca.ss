
WFS<> ==
  self::char_star<0,q>*q::BADS<> 
  or self::char_star<v,q>*q::WFS<> & v!=0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

/*
while (*s != '\0' && *s != (char)c)
         s++;
*/

void while1(ref char_star s, int c)
  requires s::WFS<>
  ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>
          or s::WFSeg<s'>*s'::char_star<c,q>*q::WFS<>; 
{
  int x=get_char(s);
  if (x!=0 && x!=c) {
    s = plus_plus_char(s);
    while1(s,c);
  }
}

