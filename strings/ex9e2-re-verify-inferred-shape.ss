
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
requires x::str<v,q>
  ensures  x::str<v,q> & res=q ;

int getChar(str x)
requires x::str<v,q>
  ensures x::str<v,q> & res=v;

HeapPred P(str a).
HeapPred Q(str a, str b).

pred_prim D<> inv self!=null;

P_v<> == self::str<v,q> * q::H_v<v>;

H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::D<> & v=0;

Q_v<s> == self::str<v,q> * q::D<> & self=s & v=0
  or self::str<v,q> * q::Q_v<s> & v!=0;


void while1(ref str s)
 requires s::P_v<> 
 ensures s::Q_v<s'>; //'
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
# ex9e2.ss

This spec goes thru with improved verifier.

 requires s::P_v<> 
 ensures s::Q_v<s'>; //'

P_v<> == self::str<v,q> * q::H_v<v>;

H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::D<> & v=0;

Q_v<s> == self::str<v,q> * q::D<> & self=s & v=0
  or self::str<v,q> * q::Q_v<s> & v!=0;

*/

