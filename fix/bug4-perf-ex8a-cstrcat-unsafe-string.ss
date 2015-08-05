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

WFS<n:int,k:int> ==
  self::str<0,q>*q::BADS<> & n=k
  or self::str<v,q>*q::WFS<n+1,k> & v>0 & n<k
  inv n<=k;

WFSeg<n:int,p> ==
  self=p & n=0
  or self::str<v,q>*q::WFSeg<n-1,p> & v>0 
  inv n>=0;

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
  requires s::WFS<n,k> & Term[k-n]
  ensures s::WFSeg<k-n,s'>*s'::str<0,q>*q::BADS<>;
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
  requires s1::str<_,q>*q::BADS<> * s2::WFS<n,k> & Term[k-n]
  ensures s1::WFSeg<k-n,pp>*pp::str<0,qq>*qq::BADS<> 
           * s2'::str<0,qqq> * qqq::BADS<> & pp=s1'; //
/*
# bug4.ss

  requires s1::str<_,q>*q::BADS<> * s2::WFS<n,k> & Term[k-n]
  ensures (exists pp: s1::WFSeg<k-n,pp>*pp::str<0,qq>*qq::BADS<> 
           * s2'::str<0,qqq> * qqq::BADS<> & pp=s1'); //

Why is there a performance bug when we used pp=s1'?
Similarly for the above..

Checking procedure while2$str~str... [omega.ml]Timeout when checking sat for 
10. Restarting Omega after ... 249 invocations Stop Omega... 249 invocations [omega.ml]Timeout when checking sat for 
10. Restarting Omega after ... 263 invocations Stop Omega... 263 invocations [omega.ml]Timeout when checking sat for 
10. Restarting Omega after ... 274 invocations Stop Omega... 274 invocations 

  requires s1::str<_,q>*q::BADS<> * s2::WFS<n,k> & Term[k-n]
  ensures s1::WFSeg<k-n,s1'>*s1'::str<0,qq>*qq::BADS<> 
  * s2'::str<0,qqq> * qqq::BADS<>; //
*/
{
  int x=getChar(s2);
  assignStr(s1,x);
  if (x!=0) {
    s2 = incStr(s2);
    s1 = incStr(s1);
    while2(s1,s2);
  }

}
