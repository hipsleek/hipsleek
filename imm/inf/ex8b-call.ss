data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2,int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
 int x = c.fst;
 return x;
}
/********************
inferred pre:    c::cell<v>@a&a<:@L 
inferred post   (exists b_1464,w_1465: c::cell<w_1465>@b_1464&w_1465=res & v=res & a<:@L & a<:b_1464)
*********************/


int goo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
  int x = foo(c);
/*********************
ctx:   c::cell<v>@[@a, @a_1495] * c'::cell<w_1503>@b_1502  & a_1495=@L & a_1495<:b_1502 & a<:@L & w_1503=res & v_1496=res  & v_1496=v & P1(a) & c'=c
*********************/
  dprint;
  return x;
}


/**
dprint(simpl): ex8b-call.ss:24: ctx:  List of Failesc Context: [FEC(0, 0, 1  [])]

Successful States:
[
 Label: []
 State:hfalse&false&{FLOW,(4,5)=__norm#E}[]
       es_orig_ante: Some(hfalse&false&{FLOW,(4,5)=__norm#E}[])
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: [P1; P2]
       es_infer_rel: [RELASS [P1]: ( P1(a)) -->  a<:@L]
 Exc:None
 ]
*/
