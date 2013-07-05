data node {
 int val;
 node next;
}

HeapPred H(node x, int v).
PostPred G(node x, int v).

bool check_sorted(node x, int v)
  infer [H,G]
  requires H(x,v)
  ensures G(x,v) & res;
{ 
  if (x==null) return true;
  else {
   int t = x.val;
   if (v<=t) return check_sorted(x.next,t);
   else {
       dprint;
       return false;
   }
 }
} 

/*
[ H(x,v)&x=null --> G(x,v),

  H(x,v)&x!=null --> x::node<val_16_918,next_16_919>@M * 
    HP_920(val_16_918@NI,v@NI) * HP_921(next_16_919,v@NI) * HP_922(v,x@NI),
  
 HP_921(next_16_919,v@NI)&v<=val_16_918 --> H(next_16_919,val_16_918),
 
 HP_920(val_16_918@NI,v@NI) * HP_922(v,x@NI) * 
  x::node<val_16_918,next_16_919>@M * G(next_16_919,val_16_918)&
  v<=val_16_918 --> G(x,v)]

===
[ H(x_947,v_948) ::= 
 x_947::node<val_16_918,next_16_919>@M * HP_920(val_16_918,v_948) * 
 HP_922(v_948,x_947) * H(next_16_919,val_16_944)&v_948<=val_16_944
 or emp&x_947=null
 ,
 G(x_952,v_953) ::= 
 HP_920(val_16_918,v_953) * HP_922(v_953,x_952) * 
 x_952::node<val_16_918,next_16_919>@M * G(next_16_919,val_16_918)&
 v_953<=val_16_918
 or emp&x_952=null
 ,
 HP_922(v,x) ::= NONE,
 HP_920(val_16_918,v) ::= NONE]
**
*/