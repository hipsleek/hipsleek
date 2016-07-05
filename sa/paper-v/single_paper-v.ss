data node{
       int val;
       node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

//ll<D> == self = null & D={}  or self::node<_, q> * q::ll<>;

lseg<p> == self = p & self!=null  or self::node<_, q> * q::lseg<p>& self!=p;
lshd<p> == p::lseg<self>*self::node<_,null>;

HeapPred H(node a).
PostPred G(node a, node b).

node last (node x)
requires x::ll<> & x!=null ensures res::lshd<x>;
//infer[H,G] requires H(x) ensures G(res,x);
{
   if (x.next==null) return x;
   else
   {
       node t = last(x.next);
       //t.val = t.val+1;
       node v = t.next;
       // dprint;
       assert v' = null assume true;//'
       return t;
       }
}
/*
{
   node y = x.next;
   if (y==null) return x;
   else {
     //assume false;
     node t = last(y);
     t.next=null;
     return t;
   }
}*/

/*
# single_paper.ss

[ H(x) --> x::node<val_20_942,next_20_943>@M * HP_944(next_20_943),

 HP_944(next_20_943)&next_20_943!=null --> H(next_20_943),

 G(t_37',next_20_943)&
  next_20_943!=null --> t_37'::node<val_25_959,next_25_960>@M * 
  GP_961(next_25_960,next_20_943@NI) * GP_962(next_20_943,t_37'@NI),

 GP_961(next_25_960,next_20_943@NI) --> emp&next_25_960=null,

 HP_944(next_20_943) * x::node<val_20_942,next_20_943>@M&res=x & 
  next_20_943=null --> G(res,x),

 x::node<val_20_942,next_20_943>@M * GP_961(next_25_960,next_20_943@NI) * 
  GP_962(next_20_943,res@NI) * res::node<val_25_959,next_25_960>@M&
  next_25_960=null --> G(res,x)]

----

GOT
===

!!! >>>>>> step 3: apply transitive implication<<<<<<
!!! >>>>>> step 3a: simplification <<<<<<
!!!  synthesize: [H,GP_962]
!!! >>>>>> step 3b: do apply_transitive_imp <<<<<<
!!! >>>>>> step 3a: simplification <<<<<<
!!!  synthesize: [HP_944,GP_961]
!!! >>>>>> step 3b: do apply_transitive_imp <<<<<<
!!! >>>>>> pre-predicates<<<<<<


Expected Order:
===============
  H,
  HP_944,
  G
  post-obligation :
   G(t_37',next_20_943)&
   next_20_943!=null --> t_37'::node<val_25_959,next_25_960>@M * 
   GP_961(next_25_960,next_20_943@NI) * GP_962(next_20_943,t_37'@NI),
  G_961/G_962
  post-obligation:
    GP_961(next_25_960,next_20_943@NI) --> emp&next_25_960=null,

Outcome below is wrong
======================
[ H(x_1001) ::= x_1001::node<val_20_942,next_20_943>@M * HP_944(next_20_943),
 G(res_1005,x_1006) ::= 
 res_1005::node<val_20_942,next_20_943>@M&res_1005=x_1006 & next_20_943=null
 or x_1006::node<val_20_1007,next_20_1008>@M * 
    GP_962(next_20_1008,res_1005) * res_1005::node<val_20_942,next_20_943>@M&
    next_20_943=null
 ,
 HP_944(next_20_1004) ::= 
 next_20_1004::node<val_20_942,next_20_943>@M * HP_944(next_20_943)
 or emp&next_20_1004=null
 ]

--pred-en-dangling

[ H(x_875) ::=  x_875::node<val_20_816,next_20_817>@M * HP_818(next_20_817),
 G(res_879,x_880) ::=  
 x_880::node<val_20_881,next_20_882>@M * HP_836(next_20_882,res_879) * 
 res_879::node<val_20_816,next_20_817>@M&next_20_817=null
 or res_879::node<val_20_816,next_20_817>@M&res_879=x_880 & next_20_817=null
 ,
 HP_818(next_20_876) ::=  
 emp&next_20_876=null
 or next_20_876::node<val_20_816,next_20_817>@M * HP_818(next_20_817)
 ,
 HP_836(next_20_944,t_945) ::=  
 emp&next_20_944!=null & next_20_944=t_945
 or next_20_944::node<val_20_940,next_20_941>@M * HP_836(next_20_941,t_945)
 ]


*/
