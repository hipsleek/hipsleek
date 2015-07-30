
data str {
  int val;
  str next;
}


str incStr(str x)
requires x::str<v,q>
  ensures  x::str<v,q> & res=q ;

int getChar(str x)
requires x::str<v,q>
  ensures x::str<v,q> & res=v;

HeapPred P(str a).
HeapPred Q(str a, str b).

P_v<d> == self::str<v,q> * q::H_v<v,d>;

H_v<v,d> == self::str<v1,q> * q::H_v<v1,d> & v!=0
  or self=d & v=0;

Q_v<s,d> == self::str<v,d>  & self=s & v=0
  or self::str<v,q> * q::Q_v<s,d> & v!=0;


void while1(ref str s)
 requires s::P_v<d> 
 ensures s::Q_v<s',d>; //'
//infer [P,Q] requires P(s) ensures Q(s,s');//'
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
# ex9e3.ss

This spec goes thru with improved verifier.

 requires s::P_v<d> 
 ensures s::Q_v<s',d>; //'


P_v<d> == self::str<v,q> * q::H_v<v,d>;

H_v<v,d> == self::str<v1,q> * q::H_v<v1,d> & v!=0
  or self=d & v=0;

Q_v<s,d> == self::str<v,d>  & self=s & v=0
  or self::str<v,q> * q::Q_v<s,d> & v!=0;

*/

