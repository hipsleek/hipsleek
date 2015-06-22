data cell {
  int x;
}

int foo(cell c)

  requires true
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
  ensures c::cell<w>@M;
{
  assume false;
  dprint;
  return 1;
}

/*
# ex8e1.ss

# I think we are missing on a recursive P2 case in below.

[RELASS [P1]: ( P1(a,v)) -->  a<:@L,
RELASS [P1]: ( P1(a,v)) -->  (a=@M | (a=@A & 1<=v) | v=0 | (v<=(0-1) & a=@A)),
RELDEFN P1: ( a<:@L & v<=(0-1) & P1(a,v) & v_1517+1=v & @M<:a_1516) -->  P1(a_1516,v_1517),
RELDEFN P1: ( 1<=v & a<:@L & P1(a,v) & v_1517+1=v & @M<:a_1516) -->  P1(a_1516,v_1517),
RELDEFN P2: ( res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 & P1(a,v)) -->  P2(a,b_1469,v,res,w_1470)]

--esl

# why is there a hole?

id: 0; caller: []; line: 15; classic: false; kind: BIND; hec_num: 1; evars: []; infer_vars: [ P1,P2]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail c::cell<v>@a&P1(a,v) & c'=c & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  c'::cell<fst_15_1443'>@L&{FLOW,(1,28)=__flow#E}[]. 
pure rel_ass: [RELASS [P1]: ( P1(a,v)) -->  a<:@L]
ho_vars: nothing?
res:  1[
   Hole[1489]&P1(a,v) & c'=c & fst_15_1443'=v & a<:@L&{FLOW,(4,5)=__norm#E}[]
   ]

# pre obtained is somewhat complex

id: 8; caller: []; line: 17; classic: false; kind: BIND; hec_num: 1; evars: []; infer_vars: [ P1,P2]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail c::cell<v>@a&v_bool_16_1462' & x'!=0 & P1(a,v) & c'=c & a<:@L & x'=v & 
v_int_17_1452'+1=v & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  c'::cell<fst_17_1453'>@M&{FLOW,(1,28)=__flow#E}[]. 
pure rel_ass: [RELASS [P1]: ( P1(a,v)) -->  (a=@M | (a=@A & 1<=v) | v=0 | (v<=(0-1) & a=@A))]
ho_vars: nothing?
res:  1[
   emp&v_bool_16_1462' & x'!=0 & P1(a,v) & c'=c & a<:@L & x'=v & 
     v_int_17_1452'+1=v & fst_17_1453'=v&{FLOW,(4,5)=__norm#E}[]
   ]

# seems like there is a false prior to post.
# why is this false not logged by --esl?

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:hfalse&false&{FLOW,(4,5)=__norm#E}[]
       es_cond_path: [1; 0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: [P1; P2]
       es_infer_rel: [RELASS [P1]: ( P1(a,v)) -->  (a=@M | (a=@A & 1<=v) | v=0 | (v<=(0-1) & a=@A)); 
                      RELASS [P1]: ( P1(a,v)) -->  a<:@L; 
                      RELASS [P1]: ( P1(a,v)) -->  a<:@L; 
                      RELDEFN P1: ( 1<=v & a<:@L & P1(a,v) & v_1518+1=v & @M<:a_1517) -->  P1(a_1517,v_1518); 
                      RELDEFN P1: ( a<:@L & v<=(0-1) & P1(a,v) & v_1518+1=v & @M<:a_1517) -->  P1(a_1517,v_1518)]
 Exc:None
 ]

========================


How was post_ref_df_new derived from post_ref_df?

!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | (v=0 & a<:@L)))]

!!! **pi.ml#702:post_ref_df:[( 
res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 & P1(a,v), 
P2(a,b_1469,v,res,w_1470))]
!!! **pi.ml#717:post_ref_df_new:[( 
res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 
& 1<=v & a<:@L & P1(a,v) & v_1517+1=v & @M<:a_1516, 
P2(a,b_1469,v,res,w_1470))]


norm_post_rel_def@1
norm_post_rel_def inp1 :post_rel_df:[( res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 & P1(a,v), P2(a,b_1469,v,res,w_1470))]
norm_post_rel_def inp2 :pre_rel_ids :[P1]
norm_post_rel_def inp3 :all_reldefns:[( res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 & P1(a,v), P2(a,b_1469,v,res,w_1470)),( 1<=v & a<:@L & P1(a,v) & v_1517+1=v & @M<:a_1516, P1(a_1516,v_1517)),( a<:@L & v<=(0-1) & P1(a,v) & v_1517+1=v & @M<:a_1516, P1(a_1516,v_1517)),( a=@M, P1(a,v))]
norm_post_rel_def@1 EXIT:[( res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 & a=@M, P2(a,b_1469,v,res,w_1470))]

*/
