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
# ex13c5a.ss

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

??

id: 2; caller: []; line: 36; classic: false; kind: PRE; hec_num: 1; evars: []; impl_vars: [v,Anon_19]; infer_vars: [ P]; c_heap: emp; others:  es_infer_obj: [@leak] globals: [@dis_err]
 checkentail P(s)&s'=s & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  s'::char_star<v,Anon_19>@L&Term[]&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    HP_1603(Anon_1602,s) * (Hole[1604])&s'=s & v=v_1601 & Anon_19=Anon_1602&
{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]

id: 8; caller: []; line: 39; classic: false; kind: PRE_REC; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ P,HP_1603]; c_heap: emp; others:  es_infer_obj: [@leak] globals: [@dis_err]
 checkentail HP_1603(Anon_1602,s) * s::char_star<v_1601,Anon_1602>@M&
v_bool_37_1598' & s_1616=s & v=v_1601 & Anon_19=Anon_1602 & x'=v & x'!=0 & 
Anon_18=v_1601 & q=Anon_1602 & s'=q & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  P(s')&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    s::char_star<v_1601,Anon_1602>@M&
v_bool_37_1598' & s_1616=s & v=v_1601 & Anon_19=Anon_1602 & x'=v & x'!=0 & 
Anon_18=v_1601 & q=Anon_1602 & s'=q&{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   ]


*/
