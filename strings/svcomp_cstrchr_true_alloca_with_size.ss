
WFS<n> ==
  self::char_star<0,q>*q::BADS<> & n=0
  or self::char_star<v,q>*q::WFS<n-1> & v!=0 
  inv n>=0;

WFSeg<p, n> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<p, n-1> & v!=0
  inv n>=0;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

/*
while (*s != '\0' && *s != (char)c)
         s++;
*/

void while1(ref char_star s, int c)
  requires s::WFS<m>
  ensures s::WFSeg<s',m>*s'::char_star<0,q>*q::BADS<>
          or s::WFSeg<s',n>*s'::char_star<c,q>*q::WFS<m-n-1>; 
{
  int x=get_char(s);
  if (x!=0 && x!=c) {
    s = plus_plus_char(s);
    while1(s,c);
  }
}

