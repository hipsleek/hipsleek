data cell {
  int val;
}

void pre_call(cell x)
  requires x::cell<_> ensures true;
  requires true ensures true;

int foo2(cell x)
  requires x!=null
  ensures res=3;
{
  pre_call(x);
  dprint;
  return 3;

}

/*
# ex22g8.aa --efa-exc -dre "heap_entail"

Successful States:
[
 Label: []
 State:htrue&x'=x & x!=null&{FLOW,(4,5)=__norm#E}[]
       es_cond_path: [0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: []
 Exc:None
 ]

Procedure foo2$cell SUCCESS.



*/
