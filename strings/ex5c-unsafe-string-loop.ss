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
  requires x::WFS<n,k,m> & Term[]
  case { 
    n!=k  -> ensures x::str<v,res> * res::WFS<n+1,k,m> & v>0;
    n=k  ->  ensures x::str<0,res> * res::BADS<m>;
  }
  requires x::BADS<m> & Term[] & m>0
  ensures x::str<v,res> * res::BADS<m-1> & v>=0;
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
void loop1(ref str s)
  requires s::WFS<n,k> 
  case {
    n=k -> requires Term[] ensures true;
    n!=k -> requires Loop ensures false;
  }
  requires s::BADS<>@L & MayLoop 
  ensures true;
{
  int x=getChar(s);
  if (x!=0) {
    loop1(s);
  }
}

void loop2(ref str s)
  requires s::WFS<n,k>@L & Loop
  ensures false;
  requires s::BADS<>@L & Loop 
  ensures false;
{
  int x=getChar(s);
  loop2(s);
}

void loop3(ref str s)
  requires s::WFS<n,k>@L & exists(i: k-n=2*i & i>=0) & Term[k-n]
  ensures true;
  requires s::WFS<n,k>@L & exists(i: k-n=2*i+1 & i>=0) & MayLoop
  ensures true;
  requires s::BADS<>@L & MayLoop 
  ensures true;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    s = incStr(s);
    loop3(s);
  }
}


