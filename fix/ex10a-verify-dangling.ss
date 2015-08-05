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
  or self::str<v,q>*q::WFS<p> & v!=0 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::str<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::str<v,q>*q::BADS<> 
  inv true;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;

void assignStr(str x,int v)
  requires x::str<_,q> & Term[]
  ensures  x::str<v,q> ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
void while1(ref str s)
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<0,p> & a=s';
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
     while ((*s++ = *s2++) != '\0')
         ;               
*/
/*
  requires s1::str<_,q>*q::BADS<> * s2::WFS<n,k> & Term[k-n]
  ensures s1::WFSeg<k-n,s1a>*s1a::str<0,s1'>*s1'::BADS<> 
     * _::str<0,s2'> *s2'::BADS<>; //
*/

void while2(ref str s1,ref str s2)
  requires s1::str<_,q>*q::BADS<> * s2::WFS<r>@L 
  ensures s1::WFSeg<s1a>*s1a::str<0,ppp>*ppp::BADS<> & s1'=ppp;
{
  int x=getChar(s2);
  assignStr(s1,x);
  s2 = incStr(s2);
  s1 = incStr(s1);
  if (x!=0) {
    while2(s1,s2);
  }
}

