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
# cyc-lseg.ss --pred-en-split

Inferred result is fine.
How come predicate synthesis option is not working?

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

The --pred-en-split option is not working, as it has same
result as above.

I wonder if we can derive, maybe using lemma synthesis?

  G(y,y') ::= G2(y) * G3(y')
  G2(y_884) ::= 
   y_884::node<next_20_873>@M * G(next_20_873)
   or emp&y_884=null
  G3(y') ::= y'=null

*/