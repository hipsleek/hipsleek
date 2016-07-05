data cell {
  int val;
}

void pre_call(cell x)
  requires x::cell<_>
  ensures true;

void pre_call2(cell x)
  requires true
  ensures true & flow __Exc;

void pre_call3(cell x)
  requires true
  ensures true & flow __Error;

int foo2(cell x)
  requires x=null
  ensures true ;
{
  pre_call(x);
  //pre_call(x);
  //int a = x.val;
  dprint;
  return 3;

}

/*
# ex21a8 --efa-exc -dre "heap_entail"

--efa-exc triggers must-err exception for pre-condition checking

id: 0; caller: []; line: 21; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_must] globals: [@err_must]
 checkentail emp&x=null & x'=x & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  x'::cell<Anon_11>&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   emp&x=null & x'=x&{FLOW,(6,10)=__Error#E}[]
   es_final_error:[do_unmatched_rhs : x'::cell<Anon_11>]
   ]


*/
