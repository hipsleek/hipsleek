
data node {
 int val;
 node next;
}

HeapPred H(node x, int v). // non-ptrs are @NI by default
PostPred G(node x, int v). // non-ptrs are @NI by default

/*
sortll<n> == self=null
 or self::node<v,q>*q::sortll<v> & n<=v
 inv true; 
*/

bool check_sorted(node x, int v)
  infer [H,G]
  requires H(x,v)
  ensures G(x,v) & res;
//requires x::sortll<v>@L ensures  res;
{ 
  if (x==null) return true;
  else {
   int t = x.val;
   if (v<=t) return check_sorted(x.next,t);
   else {
      //dprint;
       return false;
   }
 }
} 

/*
# check-sorted.ss --sa-en-pure-field 


HP_930(next_20_928,v)&v<=val_20_927 --> H(next_20_928,val_20_927)]

Should not convert to:
 HP_930(next_20_928,v) <--> H(next_20_928,val_20_927) & v<=val_20_927

Defn
====

HP_930(next_20_928,v) | v<=val_20_927 <-> H(next_20_928,val_20_927)]

HP_930(n,v) | l::node<.,n> <-> H(n,l)]


GOT which is very good but a bit ambiguous
with respecy to HP_921
-------------------------------------------
 H(x_955,v_956) ::= 
 x_955::node<val_16_943,next_16_944>@M * HP_921(next_16_944,v_956)&
   val_16_943>=v_956
 or emp&x_955=null,

 G(x_961,v_962) ::= 
 emp&x_961=null
 or x_961::node<val_16_918,next_16_919>@M * G(next_16_919,val_16_918)&
    val_16_918>=v_962,

 HP_921(next_16_957,v_958) ::= H(next_16_957,val_16_918)&v_958<=val_16_918]
--------------------------------------------
The last equation should have been:
 HP_921(next_16_957,v_958) & v_958<=val_16_918 
    <--> H(next_16_957,val_16_918)

If we confirm it before H, we would have an opportunity to inline it
during simplication
 H(x_955,v_956) & x_255!=null -->
   x_955::node<val_16_943,next_16_944>@M * HP_921(next_16_944,v_956)&
   val_16_943>=v_956
 H(x_955,v_956) & x_255!=null -->
   x_955::node<val_16_943,next_16_944>@M * H(next_16_944,val_16_943) &
   val_16_943>=v_956
This would yield a perfect result.


===================================

GOT
===

 H(x,v)&x!=null --> x::node<val_16_918,next_16_919>@M * 
  HP_920(val_16_918@NI,v@NI) * HP_921(next_16_919,v@NI) * HP_922(v,x@NI),
 HP_921(next_16_919,v@NI)&v<=val_16_918 --> H(next_16_919,val_16_918),
 H(x,v)&x=null --> G(x,v),
 HP_920(val_16_918@NI,v@NI) * HP_922(v,x@NI) * 
  x::node<val_16_918,next_16_919>@M * G(next_16_919,val_16_918)&
  v<=val_16_918 --> G(x,v),
 HP_920(val_16_918@NI,v@NI) --> emp&forall(x:(val_16_918>=v | x=null))]


BUT caused an exception during shape_infer..

Context of Verification Failure: 1 File "check-sorted.ss",Line:12,Col:10
Last Proving Location: 1 File "check-sorted.ss",Line:20,Col:14

ERROR: at _0:0_0:0 
Message: cpure.get_neq_null_svl: ?
 
ExceptionFailure("cpure.get_neq_null_svl: ?")Occurred!

Error(s) detected at main 
Stop Omega... 78 invocations Halting Reduce... 
caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("cpure.get_neq_null_svl: ?")


======================

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
