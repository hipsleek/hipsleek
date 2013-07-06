data node {
 int val;
 node next;
}

HeapPred H(node x).
PostPred G(node x).

bool check_pos(node x)
  infer [H,G]
  requires H(x)
  ensures G(x) & res;
{ 
  if (x==null) return true;
  else {
   return x.val>0 && check_pos(x.next);
  }
} 

/*
# check-pos.ss

--sa-en-pure-field 

[ H(x)&x!=null --> x::node<val_16_916,next_16_917>@M * 
  HP_918(val_16_916@NI) * HP_919(next_16_917),
 HP_919(next_16_917) --> H(next_16_917),
 HP_919(next_16_917) --> H(next_16_917),
 H(x)&x=null --> G(x),
 HP_918(val_16_916@NI) * x::node<val_16_916,next_16_917>@M * G(next_16_917)&
  0<val_16_916 --> G(x),
 HP_918(val_16_916@NI) --> emp&val_16_916>0]


GOT
===

WHY HP_969 disappeared in H?

[ H(x_968) ::= 
 H(next_16_958) * x_968::node<val_16_959,next_16_958>@M&val_16_959>0
 or emp&x_968=null
 ,
 G(x_969) ::= 
 HP_918(val_16_916) * x_969::node<val_16_916,next_16_917>@M * G(next_16_917)&
 0<val_16_916
 or emp&x_969=null
 ,
 HP_918(val_16_916) ::= NONE]


*/
