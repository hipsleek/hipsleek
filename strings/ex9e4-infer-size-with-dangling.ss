
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

P_v<d,n> == self::str<v,q> * q::H_v<v,d,n-1>
 inv n>=1;

H_v<v,d,n> == self::str<v1,q> * q::H_v<v1,d,n-1> & v!=0
  or self=d & v=0 & n=0
 inv n>=0;

Q_v<s,d,n> == self::str<v,d>  & self=s & v=0 & n=1
  or self::str<v,q> * q::Q_v<s,d,n-1> & v!=0
 inv n>=1;

relation PO(int n, int m).

void while1(ref str s)
 infer [PO]
  requires s::P_v<d,n> 
 ensures s::Q_v<s',d,m> & PO(n,m); //'
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
# ex9e4.ss

Inferred numeric outcome:

!!! **fixcalc.ml#1060:Result of fixcalc (parsed): :[ n>=1 & n=m]
!!! **pi.ml#775:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#776:>>REL POST:  PO(n,m)
!!! **pi.ml#777:>>POST:  n>=1 & n=m
!!! **pi.ml#778:>>REL PRE :  true
!!! **pi.ml#779:>>PRE :  true

# need to work on size extension @size

P_v<d> == self::str<v,q> * q::H_v<v,d>;

H_v<v,d> == self::str<v1,q> * q::H_v<v1,d> & v!=0
  or self=d & v=0;

Q_v<s,d> == self::str<v,d>  & self=s & v=0
  or self::str<v,q> * q::Q_v<s,d> & v!=0;

==>

P_v<d,n> == self::str<v,q> * q::H_v<v,d,n-1>
 inv n>=1;

H_v<v,d,n> == self::str<v1,q> * q::H_v<v1,d,n-1> & v!=0
  or self=d & v=0 & n=0
 inv n>=0;

Q_v<s,d,n> == self::str<v,d>  & self=s & v=0 & n=1
  or self::str<v,q> * q::Q_v<s,d,n-1> & v!=0
 inv n>=1;

*/

