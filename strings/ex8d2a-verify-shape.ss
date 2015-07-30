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

U<> == true;

P_v<> == self::str<v,q> * q::H_v<v>;

H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::U<> & v=0;

Q_v<s> == self::str<v,q> * q::U<> & self=s & v=0
  or self::str<v,q> * q::Q_v<s> & v!=0;



void while1(ref str s)
/* //s1
  requires s::WFS<> 
  ensures s::WFSeg<s'>*s'::str<0,q>*q::BADS<>;
*/
/* //s2
  requires s::BADS<>
  ensures s::WFSeg<s'>*s'::str<0,q>*q::BADS<>;
*/
/* //s3
requires s::P_v<> 
  ensures s::Q_v<s'>; //'
*/
infer [P,Q] requires P(s) ensures Q(s,s');//'
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


 *********************************************************
*******relational definition ********
*********************************************************
[ P(s_1571) ::= P(q_1569) * s_1571::str<v_1572,q_1569>(4,5),
 Q(s_1573,s_1574) ::=
 s_1574::str<v_1576,q_1546> * P(q_1546)&s_1574=s_1573
 or s_1573::str<Anon_1575,q_1557> * Q(q_1557,s_1574)
 (4,5)]
*************************************
                                       */


                                      /*
*********************************************************
//  ../hip ex8d-w1.ss --sa-en-pure-field
*******relational definition ********
*********************************************************
[ P(s_1599) ::= s_1599::str<v_1576,q_1577> * HP_1578(q_1577,v_1576)(4,5),
 Q(s_1604,s_1605) ::=
 s_1605::str<v,q>&s_1605=s_1604 //?? v=0
 or s_1604::str<v_1589,q_1590> * Q(q_1590,s_1605)&v_1589!=0
 (4,5),
 HP_1578(q_1602,v_1603) ::=
 q_1602::str<v_1576,q_1577> * HP_1578(q_1577,v_1576)&v_1603!=0
 or emp&v_1603=0
 (4,5)]
*************************************

                                       */
