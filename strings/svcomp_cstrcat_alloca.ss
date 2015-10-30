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

lemma_safe self::WFSeg<p> <- self::WFSeg<q>*q::WFSeg<p> .

lemma_safe self::WFS<> <-> self::WFSeg<q>*q::char_star<0,q2>*q2::BADS<> .

/*
     while (*s != '\0')
         s++;
*/

void while1(ref char_star s)
  requires s::WFS<> 
  ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;
{
  int x = get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
    while1(s);
  }
}


/*
     while ((*s++ = *s2++) != '\0')
         ;               
*/

void while2(ref char_star s1,ref char_star s2)
  requires s1::char_star<_,q> * q::BADS<> * s2::WFS<>   
  ensures s2::WFSeg<qq>*qq::char_star<0,s2'>*s2'::BADS<> * s1::WFSeg<q4>*q4::char_star<0,s1'>*s1'::BADS<>;
{
  int x=get_char(s2);
  write_char(s1,x);
  s2 = plus_plus_char(s2);
  s1 = plus_plus_char(s1);
  if (x!=0) {
    while2(s1,s2);
  }

}

