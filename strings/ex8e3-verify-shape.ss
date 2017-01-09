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


str incStr(str x)
/*
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;
*/
requires x::str<v,q>
  ensures  x::str<v,q> & res=q ;
/*
  requires x::WFS<n,k> & Term[]
  case { 
    n!=k  -> ensures x::str<v,res> * res::WFS<n+1,k> & v>0;
    n=k  ->  ensures x::str<0,res> * res::BADS<>;
  }
  requires x::BADS<> & Term[]
  ensures x::str<v,res> * res::BADS<> & v>=0;
*/

int getChar(str x)
/*
  requires x::str<v,q>@L & Term[]
  ensures res=v;
*/
requires x::str<v,q>
  ensures x::str<v,q> & res=v;
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/

HeapPred P(str a).
HeapPred Q(str a, str b).
//HeapPred U(str a).

pred_prim D<> inv self!=null;

P_v<> == self::str<v,q> * q::H_v<v>;

H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::D<> & v=0;

Q_v<s> == self::str<v,q> * q::D<> & self=s & v=0
  or self::str<v,q> * q::Q_v<s> & v!=0;


void while1(ref str s)
//infer [P,Q] requires P(s) ensures Q(s,s');//'
requires s::str<v,q> * q::H_v<v> 
ensures s::Q_v<s'>;
{
  int x=getChar(s);
  if (x!=0) {
    // dprint;
    s = incStr(s);
    //dprint;
    while1(s);
  }
}


/*
# ex8e3/slk

ERROR: at _0:0_0:0
Message: Can not find flow of str

ERROR: at ex8e3-verify-shape.ss_79:5_79:14
Message: gather_type_info_var : unexpected exception Failure("Can not find flow of str")

# Why type error for below?

D<> == true;
// pred_prim D<> inv self!=null;

*/
