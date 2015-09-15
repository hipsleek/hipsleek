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
  infer [P,@classic,@pure_field
  ]
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
# ex13c5b.ss

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
true]

====================================================================

 // POST
(2;0)HP_1603(Anon_1602)&true |#| s::char_star<v_1601,Anon_1602>@M&
v_1601=0 --> emp&
true]





*/
