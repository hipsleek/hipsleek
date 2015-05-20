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


int goo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
  int x = foo(c);
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
