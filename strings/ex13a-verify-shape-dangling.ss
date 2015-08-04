/*
 char *(cstrcat)(char *s1, const char *s2)
 {
     char *s = s1;
     while (*s != '\0')
         s++;
     while ((*s++ = *s2++) != '\0')
         ;               
     return s1;
 }

int main() {
  char *s1;
  char *s2;
  cstrcat(s1, s2);
  return 0;
}
*/

data str {
  int val;
  str next;
}

WFS<p> ==
  self::str<0,p> 
  or self::str<v,q>*q::WFS<p> & v>0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::str<v,q>*q::WFSeg<p> & v>0
  inv true;

BADS<> ==
  self::str<v,q>*q::BADS<> & v>=0
  inv true;

/* ptr ++ */
str incStr(str x)
  requires x::str<v,q>
  ensures  x::str<v,q> & res=q ;

int getChar(str x)
  requires x::str<v,q>
  ensures x::str<v,q> & res=v //& res=x+1
  ;

void updateChar(str x, int i)
  requires x::str<_,q>
  ensures x::str<i,q> 
  ;


/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/


void while1(ref str s)
  requires s::WFS<p> 
  ensures s::WFSeg<s'>*s'::str<0,p>;
{
  int x=getChar(s);
  if (x!=0) {
    // dprint;
    s = incStr(s);
    //dprint;
    while1(s);
  }
}

