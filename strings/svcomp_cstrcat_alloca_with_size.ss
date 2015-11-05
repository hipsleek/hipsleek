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

lemma_safe self::WFSeg<p,n1+n2> <- self::WFSeg<q,n1>*q::WFSeg<p,n2>.

lemma_safe self::WFS<n> <-> self::WFSeg<q,n>*q::char_star<0,q2>*q2::BADS<> .

/*
     while (*s != '\0')
         s++;
*/

void while1(ref char_star s)
  requires s::WFS<n1> 
  ensures s::WFSeg<s', n1>*s'::char_star<0,q>*q::BADS<>;
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
  requires s1::char_star<_,q> * q::BADS<> * s2::WFS<n2>   
  ensures s2::WFSeg<qq, n2>*qq::char_star<0,s2'>*s2'::BADS<> * s1::WFSeg<q4, n2>*q4::char_star<0,s1'>*s1'::BADS<>;
{
  int x=get_char(s2);
  write_char(s1,x);
  s2 = plus_plus_char(s2);
  s1 = plus_plus_char(s1);
  if (x!=0) {
    while2(s1,s2);
  }

}

