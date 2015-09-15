/*
in prelude.ss
data char_star {
  int val;
  char_star next;
}
*/

pred_prim Dangling<>
inv true;

WSS<p> ==
  self::WFSeg<q>*q::char_star<0,p> 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

WFS<> ==
  self::char_star<0,_> 
  or self::char_star<v,q>*q::WFS<> & v!=0
  inv true;

/*
BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;
*/

HeapPred P(char_star x).

void while1(ref char_star s)
  infer [P,@classic,@pure_field
  ]
  requires P(s)
  ensures true;
/*
  requires s::WFS<> 
  ensures true;
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
# ex13c.ss -dre "iprocess_a\|add_dang" 

# GOT

!!! **syn.ml#15:TODO : this proc is to add dangling references
(==sa3.ml#2771==)
add_dangling@3@2@1
add_dangling inp1 : 
  All_RA: [(0)P(s) |#|  --> s::char_star<v_1618,Anon_1619>@M * 
                            HP_1620(Anon_1619); 
           (1;0)HP_1620(Anon_1619) |#| s::char_star<v_1618,Anon_1619>@M&
            v_1618!=0 --> P(Anon_1619); 
           (2;0)HP_1620(Anon_1619) |#| s::char_star<v_1618,Anon_1619>@M&
            v_1618=0 --> emp]
add_dangling@3 EXIT: 
  All_RA: [(0)P(s) |#|  --> s::char_star<v_1618,Anon_1619>@M * 
                            HP_1620(Anon_1619); 
           (1;0)HP_1620(Anon_1619) |#| s::char_star<v_1618,Anon_1619>@M&
            v_1618!=0 --> P(Anon_1619); 
           (2;0)HP_1620(Anon_1619) |#| s::char_star<v_1618,Anon_1619>@M&
            v_1618=0 --> emp]

# EXPECTS emp to be converted to Dangling<Anon_1619>

  All_RA: [(0)P(s) |#|  --> s::char_star<v_1618,Anon_1619>@M * 
                            HP_1620(Anon_1619); 
           (1;0)HP_1620(Anon_1619) |#| s::char_star<v_1618,Anon_1619>@M&
            v_1618!=0 --> P(Anon_1619); 
           (2;0)HP_1620(Anon_1619) |#| s::char_star<v_1618,Anon_1619>@M&
            v_1618=0 --> Dangling<Anon_1619>]

[ // PRE
(0)P(s)&true |#|3  --> s::char_star<v_1601,Anon_1602>@M 
     * HP_1603(Anon_1602)& true,
// PRE_REC
(1;0)HP_1603(Anon_1602)&true |#| 
    s::char_star<v_1601,Anon_1602>@M& v_1601!=0 --> P(Anon_1602)&true,
 // POST
(2;0)HP_1603(Anon_1602)&true |#| 
    s::char_star<v_1601,Anon_1602>@M & v_1601=0 --> emp&true]
true]

---------------------------------
# without @pure_field

# missing base-case post?
*************************************
[ // PRE
(0)P(s)&
true |#|3  --> s::char_star<v_1601,Anon_1602>@M * HP_1603(Anon_1602,s@NI)&
true,
 // PRE_REC
(1;0)HP_1603(Anon_1602,s@NI)&true |#| s::char_star<v_1601,Anon_1602>@M&
true --> P(Anon_1602)&
true]
------------------------------------------------------
# with @pure_field

# missing base-case post? + fixcalc error
*************************************
[ // PRE
:fixcalc: Parse error on line 1 rest of line: ) && 1=1)
(0)P(s)&
true |#|3  --> s::char_star<v_1601,Anon_1602>@M * HP_1603(v_1601@NI,s@NI) * 
               HP_1604(Anon_1602,s@NI)&
true,
 // PRE_REC
(1;0)HP_1604(Anon_1602,s@NI)&true |#| s::char_star<v_1601,Anon_1602>@M&
v_1601!=0 --> P(Anon_1602)&

*********************************************************
[ P(s_1633) |#| emp&v_1621!=0
        or emp&v_1624=0
                ::= P(Anon_1625) * s_1633::char_star<v_1634,Anon_1625>@M
 or s_1633::char_star<v_1634,Anon_1625>@M (4,5)]
----------------

void while1(ref char_star s)
  infer [P,@classic,@pure_field]
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

iprocess_action inp1 :analize dangling
iprocess_action inp1 :split base
iprocess_action inp1 :(pre) synthesize:[HP_1603]
iprocess_action inp1 :(pre) synthesize:[P]
iprocess_action inp1 :norm seg
iprocess_action inp1 :pre, pre-oblg, post, post-oblg
iprocess_action inp1 :seq:(0,analize dangling);(0,split base);(0,pre, pre-oblg, post, post-oblg)



Relational assumptions
----------------------
  P(s) -> s::chr<v,q>*H1(q)
  H1(q) | s::chr<v,q> & v!=0 --> P(q) 
  H1(q) | s::chr<v,q> & v=0 --> emp

==> add-dangling
  P(s) -> s::chr<v,q>*H1(q)
  H1(q) | s::chr<v,q> & v!=0 --> P(q) 
  H1(q) | s::chr<v,q> & v=0 --> D(q)

==> specialize (unfold)
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
