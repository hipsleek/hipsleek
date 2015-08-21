WFS<n:int,k:int,m:int> ==
  self::char_star<0,q>*q::BADS<m> & n=k
  or self::char_star<v,q>*q::WFS<n+1,k,m> & v>0 & n<k
  inv n<=k & m>=0;

WFSeg<n:int,p> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<n-1,p> & v>0 
  inv n>=0;

BADS<m> ==
  self=null & m=0 or
  self::char_star<v,q>*q::BADS<m-1> & v>=0 
  inv m>=0;
/* 
# ex19a1.ss

  how to handle pointer arithmetic?

char_star plus_plus_char(char_star x)
  requires x::char_star<_,q>@L & Term[]
  ensures  res=q & q=x+1;

Last Proving Location: ex19a-cstrcat-mv.ss_22:0_24:25

ERROR: at ex19a-cstrcat-mv.ss_24:23_24:24
Message: TYPE ERROR 1 : Found int but expecting char_star

!!! **main.ml#1177:WARNING : Logging not done on finalize
Stop Omega... 49 invocations caught

Exception occurred: Failure("TYPE ERROR 1 : Found int but expecting char_star")
Error3(s) detected at main 

 */
void assign_char(char_star x,int v)
  requires x::char_star<_,q> & Term[]
  ensures  x::char_star<v,q> ;

int get_char(char_star x)
  requires x::char_star<v,q>@L & Term[]
  ensures res=v;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..

  below is  tail-recursive function with 
  the same effect as loop

*/

void while1(ref char_star s)
  requires s::WFS<n,k,m> 
  ensures s::WFSeg<k-n,s'>*s'::char_star<0,q>*q::BADS<m>;
{
  int x=__get_char(s);
  if (x!=0) {
    s = __plus_plus_char(s);
    while1(s);
  }
}


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

