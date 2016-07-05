
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
relation PPP(str s, str a, str b, str c,int n).
void while1(ref str s)
  infer [PPP,@leak]
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<n,b> & PPP(a,p,s',b,n) ;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
    dprint;
  }
}

/*
# ex10a6.ss

  infer [PPP]
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<n,b> & PPP(a,p,s',b,n) ;


Inferring "n" seems hard. Is there residue?

[RELDEFN PPP: ( PPP(a_1598,p,s',b_1599,n_1600) & b!=null & n!=0 & a!=null & a<a_1598) -->  PPP(a,p,s',b,n),
RELDEFN PPP: ( a_1598!=null & PPP(a_1598,p,s',b_1599,n_1600) & b!=null & n!=0 & a_1598<a) -->  PPP(a,p,s',b,n),
RELDEFN PPP: ( a!=null & PPP(a,p,s',b,n)) -->  PPP(a,p,s',b,n),
RELDEFN PPP: ( b=p & n=0 & a=s' & s'!=null) -->  PPP(a,p,s',b,n)]

# @leak inference gave better results:

!!! **pi.ml#777:>>POST:  a!=null & a=s' & p=b & 0=n


*/
