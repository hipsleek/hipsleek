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

WFS<n:int> ==
  self::str<0,q>*q::BADS<> & n=0
  or self::str<v,q>*q::WFS<n-1> & v>0 //& n>0
  inv n>=0;

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
 
void while2(ref str s1,ref str s2)
  requires s1::str<_,q>*q::BADS<> * s2::WFS<nnn> & Term[nnn] //& nnn>=0
  ensures s2::WFS<nnn> * s1::WFSeg<nnn,s1a>*s1a::str<0,ppp>*ppp::BADS<> & s1'=ppp;
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

/*
# ex8b.slk --esl (explore2)

Got a TNT error for:

  requires s1::str<_,q>*q::BADS<> * s2::WFS<n>@L & Term[n]
  ensures s1::WFSeg<n,s1a>*s1a::str<0,ppp>*ppp::BADS<> & s1'=ppp;

Termination checking result: 
(83)->(95) (MayTerm ERR: not bounded)[n]

However, there does not seem to be any logging of TNT-related
sleek proofs. 

*/
