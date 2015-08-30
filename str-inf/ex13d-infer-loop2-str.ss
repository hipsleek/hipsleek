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


void while2(ref char_star s1,ref char_star s2)
  infer [P]
  requires P(s1,s2)
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
(0)P(s1,s2)&
true --> s2::char_star<v_1613,Anon_1614>@M * HP_1615(Anon_1614,s1@NI) * 
         HP_1616(s1,s2@NI)&
true,
 // PRE
(0)HP_1616(s1,s2@NI)&
true --> s1::char_star<Anon_1623,q_1624>@M * HP_1625(q_1624,s2@NI)&
true,
 // PRE_REC
(1;0)HP_1615(Anon_1614,s1@NI) * HP_1625(q,s2@NI)&true --> P(q,Anon_1614)&
true,
 // POST
(2;0)HP_1625(q_1624,s2@NI)&s1'=q & q=q_1624 --> emp&
true,
 // POST
(2;0)HP_1615(Anon_1614,s1@NI)&s2'=Anon_1614 --> emp&
true]


  //P(s1,s2)
  int x=get_char(s2);
  //   P(s1,s2) -> s2::chr<v1,q>*H2(s1,q,s2@NI)
  // s2::chr<v1,q>*H2(s1,q,s2@NI) & x'=v1
  write_char(s1,x);
  //   H2(s1,q,s2@NI) -> s1::chr<v,q2>*H3(q2,q,s2@NI,s1@NI)  
  // s1::chr<x',q1>*s2::chr<v1,q>*H3(q2,q,s2@NI,s1@NI) & x'=v1
  s2 = plus_plus_char(s2);
  // s1::chr<x',q1>*s2::chr<v1,q>*H3(q2,q,s2@NI,s1@NI) & x'=v1 & s2'=q2
  s1 = plus_plus_char(s1);
  // s1::chr<x',q1>*s2::chr<v1,q>*H3(q2,q,s2@NI,s1@NI) & x'=v1 & s2'=q2 & s1'=q1
  if (x!=0) {
    // s1::chr<x',q1>*s2::chr<v1,q>*H3(q2,q,s2@NI,s1@NI) & x'=v1 & s2'=q2 & s1'=q1 & x'!=0
         |- P(s1',s2')
    while2(s1,s2);
    //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<v1,q>  & x'=v & x'!=0 & s2'=q2 & s1'=q1 --> P(s1',s2')
    // s1::chr<x',s1'>*s2::chr<v1,s2'> & x'=v1 & s2'=q & s1'=q1 & x'!=0
         |- htrue
    // emp & x'=v1 & s2'=q & s1'=q1 & x'!=0
  }
  // s1::chr<x',q1>*s2::chr<v1,q>*H3(q2,q,s2@NI,s1@NI) & x'=v1 & s2'=q2 & s1'=q1 & x'=0
  //     |- htrue
  //     H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<x',q> & x'=0 --> emp
  // emp & x'=0 & s2'=q & s1'=q1 & x'!=0
}

  //   # relational assumptions
  //   P(s1,s2) -> s2::chr<v1,q>*H2(s1,q,s2@NI)
  //   H2(s1,q,s2@NI) -> s1::chr<v,q2>*H3(q2,q,s2@NI,s1@NI)  
  //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<v1,q>  & x'=v & x'!=0 & s2'=q2 & s1'=q1 --> P(s1',s2')
  //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<x',q> & x'=0 --> emp

  //   # add-dangling
  //   P(s1,s2) -> s2::chr<v1,q>*H2(s1,q,s2@NI)
  //   H2(s1,q,s2@NI) -> s1::chr<v,q2>*H3(q2,q,s2@NI,s1@NI)  
  //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<v1,q>  & x'=v & x'!=0 & s2'=q2 & s1'=q1 --> P(s1',s2')
  //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<x',q> & x'=0 --> D(q2)*D(q1)

  //   # in-line
  //   P(s1,s2) -> s2::chr<v1,q>*s1::chr<v,q2>*H3(q2,q,s2@NI,s1@NI)  
  //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<v1,q>  & x'=v & x'!=0 & s2'=q2 & s1'=q1 --> P(s1',s2')
  //   H3(q2,q,s2@NI,s1@NI) | s1::chr<x',q1>*s2::chr<x',q> & x'=0 --> D(q2)*D(q1)

  //   # specialize
  //   P(s1,s2) -> s2::chr<x',q>*s1::chr<v,q2>*P(s1',s2')  & x'=v & x'!=0 & s2'=q2 & s1'=q1
  //   P(s1,s2) -> s2::chr<x',q>*s1::chr<x',q2>* D(q2)*D(q1) & x'=0

  //   # tidy
  //   P(s1,s2) -> s2::chr<x',s2'>*s1::chr<x',s1'>*P(s1',s2') & x'!=0 & s2'=q2 & s1'=q1
  //   P(s1,s2) -> s2::chr<x',q>*s1::chr<x',q2>* D(q2)*D(q1) & x'=0

  //   # parameterize-dangling
  //   P(s1,s2,q2,q1) -> s2::chr<x',s2'>*s1::chr<x',s1'>*P(s1',s2',q2,q1) & x'!=0 & s2'=q2 & s1'=q1
  //   P(s1,s2,q2,q1) -> s2::chr<x',q>*s1::chr<x',q2> & x'=0

 
  //   # unknown-segment
  //   P(s1,s2,d1,d2) -> U(s1,s2,q1,q2) * q1::chr<0,d1>*q2::chr<0,d2>

  //   # synthesize segmented
  //   P(s1,s2,d1,d2) -> U(s1,s2,q1,q2) * q1::chr<0,d1>*q2::chr<0,d2>
  //   U(s1,s2,q1,q2) -> s1=q1 & s2=q2
  //   U(s1,s2,q1,q2) -> s2::chr<x',qq2>*s1::chr<x',qq1> * U(qq1,qq2,q1,q2) & x'!=0

  //   # split-predicate
  //   U(s1,s2,q1,q2) -> U1(s1,q1) * U2(s2,q2)
  //   U1(s1,q1) -> s1=q1 
  //   U1(s1,q1) -> s1::chr<x',qq1> * U1(qq1,q1) & x'!=0
  //   U1(s2,q2) -> s2=q2 
  //   U1(s2,q2) -> s2::chr<x',qq2> * U1(qq2,q2) & x'!=0

  //   # re-use predicate
  //   P(s1,s2,d1,d2) -> U1(s1,q1)*U1(s2,q2) * q1::chr<0,d1>*q2::chr<0,d2>
  //   U1(s1,q1) -> s1=q1 
  //   U1(s1,q1) -> s1::chr<x',qq1> * U1(qq1,q1) & x'!=0

*/

