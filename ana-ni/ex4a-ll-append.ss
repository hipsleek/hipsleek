data node {
  int val;
  node next;
}


relation R(node x).
relation P(node x).


node append (node x,node y)
  infer [@ana_ni,R,P]
  requires R(x) & P(y)
  ensures true;
{
  /* if (x.next==null){
    x.next = y;
    return x;
  }
   else{
     x = append(x.next, y);
     return x;
   }
  */
  if (x.next == y){
    dprint;
    return x;
  }
  return y;
 }


/*
Why this entailment generates assumptions but ex4a1 does not?


es_infer_rel: [RELASS [R]: ( R(x)) -->  2<=x; 
                  RELASS [R]: ( R(x)) -->  2<=x]

==>
es_infer_rel: [RELASS [R]: ( R(x)) -->  2<=x; 
                  RELASS [R]: ( P(y)) -->  2<=y]

id: 6; caller: []; line: 14; classic: false; kind: POST; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ R,P]; c_heap: emp; others:  es_infer_obj: [@ana_ni] globals: [@flow,@ver_post,@ana_ni]
 checkentail (exists v_node_25_1690': emp&
!(v_bool_25_1691') & P(y) & R(x) & y'=y & x'=x & 2<=x & v_node_25_1690'>1 & 
v_node_25_1690'!=y' & res=y' & MayLoop[]&{FLOW,(4,5)=__norm#E}[])
 |-  htrue&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    emp&
!(v_bool_25_1691') & P(y) & R(x) & y'=y & x'=x & 2<=x & v_node_25_1712>1 & 
v_node_25_1712!=y' & res=y'&{FLOW,(4,5)=__norm#E}[]
   es_gen_impl_vars(E): []
   es_infer_rel: [RELASS [R]: ( R(x)) -->  2<=x; 
                  RELASS [R]: ( R(x)) -->  2<=x]
   ]


 */

