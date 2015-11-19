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

lemma_safe self::WFS<n> -> self::BADS<>.

void while1(ref char_star dst, ref char_star src)
  requires dst::BADS<> * src::WFS<n2>
  ensures src::WFSeg<qq,n2>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp,n1>*pp::char_star<0,dst'>*dst'::BADS<>;
{
  char_star s = dst;
  int y = get_char(src);
  dst = plus_plus_char(dst);
  src = plus_plus_char(src); 
  write_char(s, y);
  int x = get_char(s);
  if (x!=0) {
    while1(dst, src);
  }
}
