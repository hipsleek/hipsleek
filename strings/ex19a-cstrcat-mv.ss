
data char_star {
  int val;
  char_star next;
}

WFS<n:int,k:int,m:int> ==
  self::char_star<0,q>*q::EXTRA<m> & n=k
  or self::char_star<v,q>*q::WFS<n+1,k,m> & v>0 & n<k
  inv n<=k & m>=0;

WFSeg<n:int,p> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<n-1,p> & v>0 
  inv n>=0;

EXTRA<m> ==
  self=null & m=0 or
  self::char_star<v,q>*q::EXTRA<m-1> & v>=0 
  inv m>=0;

char_star plus_plus_char(char_star x)
  requires x::char_star<_,q>@L & Term[]
  ensures  res=q ;

void assign_char(char_star x,int v)
  requires x::char_star<_,q> & Term[]
  ensures  x::char_star<v,q> ;

int get_char(char_star x)
  requires x::char_star<v,q>@L & Term[]
  ensures res=v ;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..

  below is  tail-recursive function with 
  the same effect as loop

*/

void while1(ref char_star s)
  requires s::WFS<n,k,m> 
  ensures s::WFSeg<k-n,s'>*s'::char_star<0,q>*q::EXTRA<m> ;
{
  int x=get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
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

