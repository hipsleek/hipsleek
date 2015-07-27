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

WFS<> ==
  self::str<0,q>*q::BADS<> 
  or self::str<v,q>*q::WFS<> & v>0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::str<v,q>*q::WFSeg<p> & v>0
  inv true;

BADS<> ==
  self::str<v,q>*q::BADS<> & v>=0
  inv true;


str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;
/*
  requires x::WFS<n,k> & Term[]
  case { 
    n!=k  -> ensures x::str<v,res> * res::WFS<n+1,k> & v>0;
    n=k  ->  ensures x::str<0,res> * res::BADS<>;
  }
  requires x::BADS<> & Term[]
  ensures x::str<v,res> * res::BADS<> & v>=0;
*/

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
  requires s::WFS<> 
  ensures s::WFSeg<s'>*s'::str<0,q>*q::BADS<>;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}
/*
# ex8d.slk

void while1(ref str s)
  requires s::WFS<> 
  ensures s::WFSeg<s'>*s'::str<0,q>*q::BADS<>;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

Can shape infer handle this using
 infer [P,Q]
 requires P(s)
 ensures Q(s,s');


*/

/*
     while ((*s++ = *s2++) != '\0')
         ;               
*/
void while2(ref str s1,ref str s2)
  requires s1::str<_,q>*q::BADS<> * s2::WFS<>@L 
  ensures s1::WFSeg<s1a>*s1a::str<0,ppp>*ppp::BADS<> & s1'=ppp;
/*
  requires s1::str<_,q>*q::BADS<> * s2::WFS<n,k> & Term[k-n]
  ensures s1::WFSeg<k-n,s1a>*s1a::str<0,s1'>*s1'::BADS<> 
     * _::str<0,s2'> *s2'::BADS<>; //
*/
{
  int x=getChar(s2);
  assignStr(s1,x);
  s2 = incStr(s2);
  s1 = incStr(s1);
  if (x!=0) {
    while2(s1,s2);
  }
}
