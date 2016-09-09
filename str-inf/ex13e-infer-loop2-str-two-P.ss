/*
in prelude.ss
data char_star {
  int val;
  char_star next;
}
*/

WSS<p> ==
  self::WFSeg<q>*q::char_star<0,p> 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

/*
BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;
*/

HeapPred P(char_star x, char_star y).
HeapPred P1(char_star x).
HeapPred P2(char_star x).


void while2(ref char_star s1,ref char_star s2)
  infer [P1,P2]
  requires P1(s1)*P2(s2)
  ensures true;
  /*
  requires s1::char_star<_,q>*q::BADS<> * s2::WSS<p>@L 
  ensures s1::WFSeg<s1a>*s1a::char_star<0,s1'>*s1'::BADS<>;
  */
{
  int x=get_char(s2);
  write_char(s1,x);
  s2 = plus_plus_char(s2);
  s1 = plus_plus_char(s1);
  if (x!=0) {
    while2(s1,s2);
  }
}


/*
# ex13d.ss

[ // PRE
(0)P2(s2)&true --> s2::char_star<v_1616,Anon_1617>@M * HP_1618(Anon_1617)&
true,
 // PRE
(0)P1(s1)&true --> s1::char_star<Anon_1625,q_1626>@M * HP_1627(q_1626)&
true,
 // PRE_REC
(1;0)HP_1627(q)&true --> P1(q)&
true,
 // PRE_REC
(1;0)HP_1618(Anon_1617)&true --> P2(Anon_1617)&
true,
 // POST
(2;0)HP_1627(q_1626)&s1'=q & q=q_1626 --> emp&
true,
 // POST
(2;0)HP_1618(Anon_1617)&s2'=Anon_1617 --> emp&
true]


  //P1(s1)*P2(s2)
  int x=get_char(s2);
  //   P2(s) -> s::chr<v1,q>*H2(q)
  // P1(s1)*s2::chr<v1,q>*H2(q) & x'=v1
  write_char(s1,x);
  //   P1(s) -> s::chr<v,q>*H1(q)
  // s1::chr<x',q1>*H1(q1)*s2::chr<v1,q>*H2(q) & x'=v1
  s2 = plus_plus_char(s2);
  // s1::chr<x',q1>*H1(q1)*s2::chr<v1,q>*H2(q) & x'=v1 & s2'=q & s1'=s1
  s1 = plus_plus_char(s1);
  // s1::chr<x',q1>*H1(q1)*s2::chr<v1,q>*H2(q) & x'=v1 & s2'=q & s1'=q1
  if (x!=0) {
    // s1::chr<x',s1'>*H1(s1')*s2::chr<v1,s2'>*H2(s2') & x'=v1 & s2'=q & s1'=q1 & x'!=0
         |- P1(s1') * P2(s2')
    while2(s1,s2);
    //   H1(s1') | s1::chr<x',s1'> & x'!=0 --> P1(s1')
    //   H2(s2') | s2::chr<v1,s1'> & x'=v1 & x'!=0 --> P2(s2')
    // s1::chr<x',s1'>*s2::chr<v1,s2'> & x'=v1 & s2'=q & s1'=q1 & x'!=0
         |- htrue
    // emp & x'=v1 & s2'=q & s1'=q1 & x'!=0
  }
  // s1::chr<x',q1>*H1(q1)*s2::chr<x',q>*H2(q) & x'=0 & s2'=q & s1'=q1 & x'!=0
  //     |- htrue
  //     H1(s1') | s1::chr<x',s1'> & x'=0 --> emp
  //     H2(s2') | s2::chr<x',s1'> & x'=0 --> emp
  // emp & x'=0 & s2'=q & s1'=q1 & x'!=0
}

  //   P2(s) -> s::chr<v1,q>*H2(q)
  //   P1(s) -> s::chr<v,q>*H1(q)
  //   H1(s1') | s1::chr<x',s1'> & x'!=0 --> P1(s1')
  //   H2(s2') | s2::chr<v1,s1'> & x'=v1 & x'!=0 --> P2(s2')
  //   H1(s1') | s1::chr<x',s1'> & x'=0 --> emp
  //   H2(s2') | s2::chr<x',s1'> & x'=0 --> emp

???
==>
  P(s) -> s::chr<v,q> * P(q) & v!=0
  P(s) -> s::chr<v,q> * D(q) & v=0

==>
  P(s,d) -> s::chr<v,q> * P(q,d) & v!=0
  P(s,d) -> s::chr<v,d> & v=0

==>
  P(x,d) -> U(x,q) * q::chr<0,d>

==>
  P(x,d) -> U(x,q) * q::chr<v,d>
  U(x,q) -> x=q
  U(x,q) -> x::chr<v,q1>*U(q1,q) & v!=0


*/

