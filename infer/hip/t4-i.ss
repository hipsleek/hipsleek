data node {
  int val;
  node next;
}

int hd0(ref node x)
 infer [x] 
 ensures true; //'
/*
   requires x::node<inf1,inf2>
   ensures res=inf1;
*/
{
  return x.val;
}

/*
TODO: should convert EInfer to EBase

OLD SPECS:  EInfer [x]
   EAssume 1::ref [x]
     true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EAssume 1::ref [x]
   true & inf_next_18_512=x' & res=inf_val_19_517 & {FLOW,(20,21)=__norm}

*/
