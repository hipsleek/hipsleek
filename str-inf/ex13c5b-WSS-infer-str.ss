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

id: 11; caller: []; line: 30; classic: true; kind: POST; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ P,HP_1603,HP_1604,P]; c_heap: emp; others:  es_infer_obj: [@leak,@pure_field] globals: [@flow,@ver_post,@leak]
 checkentail HP_1603(v_1601,s) * s::char_star<v_1601,Anon_1602>@M * (htrue)&
q=Anon_1602 & Anon_18=v_1601 & v!=0 & Anon_19=Anon_1602 & v=v_1601 & 
s_1617=s & v_bool_37_1598' & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  htrue&{FLOW,(4,5)=__norm#E}[]. 
hprel_ass: [ (1;0)HP_1603(v_1601,s)&
  Anon_18=v_1601 & v=v_1601 & s_1617=s & v!=0 |#| s::char_star<v_1601,Anon_1602>@M&
  (q=Anon_1602 | Anon_19=Anon_1602) --> emp]
ho_vars: nothing?
res:  1[
    emp&
q=Anon_1602 & Anon_18=v_1601 & v!=0 & Anon_19=Anon_1602 & v=v_1601 & 
s_1617=s & v_bool_37_1598'&{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]

id: 12; caller: []; line: 30; classic: true; kind: POST; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ P,HP_1603,HP_1604]; c_heap: emp; others:  es_infer_obj: [@leak,@pure_field] globals: [@flow,@ver_post,@leak]
 checkentail HP_1603(v_1601,s) * HP_1604(Anon_1602,s) * s::char_star<v_1601,Anon_1602>@M&
!(v_bool_37_1598') & s'=s & v=v_1601 & Anon_19=Anon_1602 & v=0 & MayLoop[]&
{FLOW,(4,5)=__norm#E}[]
 |-  htrue&{FLOW,(4,5)=__norm#E}[]. 
hprel_ass: [ (2;0)HP_1603(v_1601,s)&
  s'=s & v=v_1601 & v=0 |#| s::char_star<v_1601,Anon_1602>@M&
  Anon_19=Anon_1602 --> emp,
 (2;0)HP_1604(Anon_1602,s)&
  s'=s & Anon_19=Anon_1602 |#| s::char_star<v_1601,Anon_1602>@M&
  (v=0 | v=v_1601) --> emp]
ho_vars: nothing?
res:  1[
    emp&!(v_bool_37_1598') & s'=s & v=v_1601 & Anon_19=Anon_1602 & v=0&
{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]



*/
