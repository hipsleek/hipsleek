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
relation P(int a, int b, int c,int d, int e).

void while1(ref str s)
  infer [P]
  requires s::WFS<n,k,m> 
  ensures s::WFSeg<n1,s'>*s'::str<0,q>*q::BADS<m> & P(m1,n1,n,k,m);
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
# ex18a.ss

Expects: n1=n-k & m1=m

!!! **fixcalc.ml#1023:Input of fixcalc: :P:={[n,k,m] -> [m1_1487,n1_1383] -> []: (n1_1383=0 && k=n && 0<=m ||  (exists (n1_1473: (exists (m1_1472: (exists (n_1458:n=n_1458-(1) && n_1458<=k && P(n_1458,k,m,m1_1472,n1_1473))) ))  && n1_1383=n1_1473+1 && 0<=n1_1473))  && 0<=m)
};
bottomupgen([P], [2], SimHeur);
!!! **fixcalc.ml#386:svls (orig):[m1_1487,n,P,k,n1_1383,m]
!!! **fixcalc.ml#387:svls (from parse_fix):[m,n1_1383,n,k]
!!! **fixcalc.ml#1051:Result of fixcalc (parsed): :[ n1_1383>=0 & m>=0 & n1_1383+n=k]

P:={[n,k,m] -> [m1_1487,n1_1383] -> []: 
 (n1_1383=0 && k=n && 0<=m ||  
 (exists (n1_1473: (exists (m1_1472: (exists (n_1458:
   n =n_1458-(1) && n_1458<=k && P(n_1458,k,m,m1_1472,n1_1473))) ))  
    && n1_1383=n1_1473+1 && 0<=n1_1473))  && 0<=m)
};

 */
