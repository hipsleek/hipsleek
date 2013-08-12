data node {
  node next;
}

HeapPred H(node x).
HeapPred G(node y,node@NI z).

ll<> == self=null
  or self::node<q>*q::ll<>;

void trav(ref node y)
  infer [H,G]
  requires H(y)
   ensures G(y,y');
/*
  requires y::ll<>
  ensures y::ll<> & y'=null;
*/
{  if (y!=null) {
     y=y.next;
     trav(y);
   }
}


/*
# cyc-lseg.ss 

Obtained
--------

[ G(y_884,y_885) ::= 
 y_884::node<next_20_873>@M * G(next_20_873,y_885)
 or emp&y_884=y_885 & y_885=null & y_884=null
 ,
 H(y_883) ::= 
 H(next_20_881) * y_883::node<next_20_881>@M
 or emp&y_883=0
 ]

I wonder if we can derive:

  G(y,y') ::= G2(y) & y'=null
 G(y_884,y_885) ::= 
 y_884::node<next_20_873>@M * G(next_20_873,y_885)
 or emp&y_884=y_885 & y_885=null & y_884=null



--pred-en-equiv reuse of equivalent predicate
definition not working properly since G/H identical to ll.
Is this option working?
 
[ G(x_882) ::= 
 x_882::node<next_20_872>@M * G(next_20_872)
 or emp&x_882=null
 ,
 H(x_881) ::= 
 H(next_20_879) * x_881::node<next_20_879>@M
 or emp&x_881=null
 ]


*/