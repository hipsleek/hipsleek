/*
data str {
  int val;
  str next;
}
*/

data chr_star {
  int val;
  chr_star next;
}
chr_star plus_plus_char(chr_star x)
requires x::chr_star<_,q>@L & Term[] 
ensures  res=q ;

int get_char(chr_star x)
  requires x::chr_star<v,_>@L & Term[]
  ensures res=v;

void write_char(chr_star x, int v)
  requires x::chr_star<_,q> & Term[]
  ensures x::chr_star<v,q>;

WFS<> ==
  self::chr_star<0,q>*q::BADS<> 
  or self::chr_star<v,q>*q::WFS<> & v!=0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::chr_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::chr_star<v,q>*q::BADS<> 
  inv true;

/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
void while1(ref chr_star s)
  requires s::WFS<> 
  ensures s::WFSeg<s'>*s'::chr_star<0,q>*q::BADS<>;
{
  // s::WFS<> 
 // s::WFS<>  --> s::chr_star<v,_>@L 
 // s::chr_star<0,q>*q::BADS<> 
 // or s::chr_star<w,q>*q::WFS<> & w!=0 --> s::chr_star<v,_>@L 
  int x=get_char(s);
  // s::chr_star<0,q>*q::BADS<> & x=0
  // or s::chr_star<w,q>*q::WFS<> & w!=0  & x=w
  if (x!=0) {
    dprint;
    // s::chr_star<w,q>*q::WFS<> & w!=0  & x=w
    s = plus_plus_char(s);
    dprint;
    while1(s);
    dprint;
  }
}

/*
     while ((*s++ = *s2++) != '\0')
         ;               
*/
void while2(ref chr_star s1,ref chr_star s2)
  requires s1::chr_star<_,q>*q::BADS<> * s2::WFS<> 
  ensures s1::WFSeg<q2>*q2::chr_star<0,qq>*qq::BADS<> 
    * s2'::chr_star<0,_> & s1'=q2; 
{
  int x=get_char(s2);
  write_char(s1,x);
  if (x!=0) {
    //dprint;
    s2 = plus_plus_char(s2);
    s1 = plus_plus_char(s1);
    while2(s1,s2);
  }

}

