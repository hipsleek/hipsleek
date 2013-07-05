data node{
       int val;
       node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

//ll<D> == self = null & D={}  or self::node<_, q> * q::ll<>;

lseg<p> == self = p & self!=null  or self::node<_, q> * q::lseg<p>& self!=p;
lshd<p> == p::lseg<self>*self::node<_,null>;

HeapPred H(node a).
HeapPred G(node a, node b).

node last (node x)
//requires x::ll<> & x!=null ensures res::lshd<x>;
infer[H,G] requires H(x) ensures G(res,x);
{
   if (x.next==null) return x;
   else
   {
       node t = last(x.next);
       //t.val = t.val+1;
       node v = t.next;
       dprint;
       assert v' = null assume true;
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

[ x::node<val_20_816,next_20_817>@M&res=x & next_20_817=null --> G(res,x),
 HP_818(next_20_817)&next_20_817=null --> emp,
 H(x) --> x::node<val_20_816,next_20_817>@M * HP_818(next_20_817),
 HP_818(next_20_817)&next_20_817!=null --> H(next_20_817),
 G(t_37',next_20_817)&
  next_20_817!=null --> t_37'::node<val_25_833,next_25_834>@M * 
  HP_835(next_25_834,next_20_817@NI) * HP_836(next_20_817,t_37'@NI),
 HP_835(next_25_834,next_20_817@NI) --> emp&next_25_834=null,
 x::node<val_20_816,next_20_817>@M * HP_836(next_20_817,res@NI) * 
  res::node<val_25_833,next_25_834>@M&next_25_834=null --> G(res,x),
 HP_835(next_25_834,next_20_817@NI)&next_25_834=null --> emp]


[ H(x_875) ::=  x_875::node<val_20_816,next_20_817>@M * HP_818(next_20_817),
 G(res_879,x_880) ::=  
 res_879::node<val_20_816,next_20_817>@M&res_879=x_880 & next_20_817=null
 or x_880::node<val_20_881,next_20_882>@M * HP_836(next_20_882,res_879) * 
    res_879::node<val_20_816,next_20_817>@M&next_20_817=null
 ,
 HP_818(next_20_876) ::=  
 next_20_876::node<val_20_816,next_20_817>@M * HP_818(next_20_817)
 or emp&next_20_876=null
 ,
 HP_836(next_20_944,t_945) ::=  
 emp&next_20_944!=null & next_20_944=t_945
 or next_20_944::node<val_20_940,next_20_941>@M * HP_836(next_20_941,t_945)
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
