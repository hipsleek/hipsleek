struct node {
  struct node* next;
};

/*@
HeapPred H(node x).
  HeapPred G(node z).
*/
/*@
ll<> == self=null
 or self::node<q>*q::ll<>;
*/

void trav(struct node* x)
/*@
  infer [H,G]
  requires H(x)
  ensures G(x);//'
*/
/*
  requires x::ll<>
  ensures x::ll<>;
*/
{  if (x) {
     x=x->next;
     trav(x);
   }
}



/*
# cyc-lseg.ss --predcyc-sl-en-equiv

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
