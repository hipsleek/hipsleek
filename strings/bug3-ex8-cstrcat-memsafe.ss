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

WFS<n:int,k:int,m:int> ==
  self::str<0,q>*q::BADS<m> & n=k
  or self::str<v,q>*q::WFS<n+1,k,m> & v>0 & n<k
  inv n<=k & m>=0;

WFSeg<n:int,p> ==
  self=p & n=0
  or self::str<v,q>*q::WFSeg<n-1,p> & v>0 
  inv n>=0;

BADS<m> ==
  self=null & m=0 or
  self::str<v,q>*q::BADS<m-1> & v>=0 
  inv m>=0;

/*

# bug3.ss

WARNING: ex8-cstrcat-memsafe.ss_43:2_46:3:WARNING : case construct has missing scenario
Found : : (n<k | n=k)
Added : : Term[] & not(((n<k | n=k)))

why is Term[] added?
*/

str incStr(str x)
  requires x::WFS<n,k,m> & Term[]
  case { 
    n<k  -> ensures x::str<v,res> * res::WFS<n+1,k,m> & v>0;
    n=k  ->  ensures x::str<0,res> * res::BADS<m>;
  }
  requires x::BADS<m> & Term[] & m>0
  ensures x::str<v,res> * res::BADS<m-1> & v>=0;

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
  requires s::WFS<n,k,m> & Term[k-n]
  ensures s::WFSeg<k-n,s'>*s'::str<0,q>*q::BADS<m>;
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
void while2(ref str s1,ref str s2)
  requires s1::str<_,q>*q::BADS<m> * s2::WFS<n,k,m2> & Term[k-n] & m>k-n
  ensures s1::WFSeg<k-n,qz>*q::str<0,qq>*qq::BADS<m-(k-n)> * s2'::str<0,_> & s1'=q; 
{
  int x=getChar(s2);
  assignStr(s1,x);
  if (x!=0) {
    s2 = incStr(s2);
    s1 = incStr(s1);
    while2(s1,s2);
  }

}
