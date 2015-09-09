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

HeapPred P(char_star x).

void while1(ref char_star s)
  infer [P,@classic,@pure_field]
  requires P(s)
  ensures true;
/*
  requires s::WSS<p> 
  ensures s::WFSeg<s'>*s'::char_star<0,p> ;
*/
{
  int x=get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
    while1(s);
  }
}

/*
# ex13c.ss

[ // PRE
(0)P(s)&true --> s::char_star<v_1601,Anon_1602>@M * HP_1603(Anon_1602)&
true,
 // PRE_REC
(1;0)HP_1603(Anon_1602)&true --> P(Anon_1602)&
true,
 // POST
(2;0)HP_1603(Anon_1602)&true --> emp&
true]
----------------



void while1(ref char_star s)
  infer [P]
  requires P(s)
  ensures true;
{
  int x=get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
    while1(s);
  }
}

  // P(s) 
  //   |- s::chr<v,q>@L
  int x=get_char(s);
  //   P(s) -> s::chr<v,q>*H1(q)
  // s::chr<v,q>*H1(q) & x'=v & s'=s
  if (x!=0) {
    // s::chr<v,q>*H1(q) & x'=v & v!=0 & s'=s
    //   |- s::chr<v,q>
    s = plus_plus_char(s);
    // s::chr<v,q>*H1(q) & x'=v & v!=0 & s'=q
    //   |- P(s')
    while1(s);
    //   H1(q) | s::chr<v,q> & v!=0 --> P(q) 
    // s::chr<v,q> & x'=v & v!=0 & s'=q
    //   |- htrue
    // emp & x'=v & v!=0 & s'=q
  }
  // s::chr<v,q>*H1(q) & x'=v & v=0
  //   |- htrue
  //   H1(q) | s::chr<v,q> & v=0 --> emp 
  // emp & x'=v & v=0
}

  P(s) -> s::chr<v,q>*H1(q)
  H1(q) | s::chr<v,q> & v!=0 --> P(q) 
  H1(q) | s::chr<v,q> & v=0 --> emp

==> add-dangling
  P(s) -> s::chr<v,q>*H1(q)
  H1(q) | s::chr<v,q> & v!=0 --> P(q) 
  H1(q) | s::chr<v,q> & v=0 --> D(q)

==> specialize
  P(s) -> s::chr<v,q> * P(q) & v!=0
  P(s) -> s::chr<v,q> * D(q) & v=0

==> parameterize-dangling
  P(s,d) -> s::chr<v,q> * P(q,d) & v!=0
  P(s,d) -> s::chr<v,d> & v=0

==> unknown segment
  P(x,d) -> U(x,q) * q::chr<0,d>

==> segmented-pred
  P(x,d) -> U(x,q) * q::chr<0,d>
  U(x,q) -> x=q
  U(x,q) -> x::chr<v,q1>*U(q1,q) & v!=0

[ // PRE
(0)P(s)&true --> s::char_star<v_1601,Anon_1602>@M * HP_1603(Anon_1602)&
true,
 // PRE_REC
(1;0)HP_1603(Anon_1602)&true --> P(Anon_1602)&
true]

id: 12; caller: []; line: 29; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ P,HP_1603]; c_heap: emp; others: [] globals: [@flow,@ver_post]
 checkentail HP_1603(Anon_1602) * s::char_star<v_1601,Anon_1602>@M&
!(v_bool_36_1598') & s'=s & v=v_1601 & Anon_19=Anon_1602 & v=0 & MayLoop[]&
{FLOW,(4,5)=__norm#E}[]
 |-  htrue&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    HP_1603(Anon_1602) * s::char_star<v_1601,Anon_1602>@M&
!(v_bool_36_1598') & s'=s & v=v_1601 & Anon_19=Anon_1602 & v=0&
{FLOW,(4,5)=__norm#E}[]
   ]



void while2(ref char_star s1,ref char_star s2)
  requires s1::char_star<_,q>*q::BADS<> * s2::WSS<p>@L 
  ensures s1::WFSeg<s1a>*s1a::char_star<0,s1'>*s1'::BADS<>;
{
  int x=get_char(s2);
  write_char(s1,x);
  s2 = plus_plus_char(s2);
  s1 = plus_plus_char(s1);
  if (x!=0) {
    while2(s1,s2);
  }
}
*/

/*
# ex12c.ss

Using segment:




*/
