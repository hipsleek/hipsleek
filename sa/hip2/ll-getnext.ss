/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

HeapPred H(node a).
HeapPred G(node a,node b).

/* function to delete the node after the head in a circular list */
node get_next(node x)
/*
   requires x::node<_,q>
   ensures x::node<_,q> & res=q;
*/
infer [H,x,G] 
requires H(x)
ensures G(x,res);
/*
[ H(x)&true --> x::node<val_26_781,next_26_782>@M * (HP_783(next_26_782))&true,
 (HP_783(res)) * x::node<val_26_781,res>@M&true --> G(x,res)&true]


Why did we have:

 [ H(x_799) ::= x_799::node<val_26_781,next_26_782>@M& XPURE(HP_786(next_26_782)),
 G(x_800,res_801) ::= 
 emp& XPURE(HP_786(res_801))
 or x_800::node<val_26_781,res_801>@M& XPURE(HP_786(res_801))
 ]

Should it not be:

 G(x_800,res_801) ::= 
    x_800::node<val_26_781,res_801>@M& XPURE(HP_786(res_801))

*/
{
	node tmp;
	tmp = x.next;
        dprint;
        return tmp;
}
/*
Why is there a spurious  XPURE(HP_786(next_23_782))?

[ H(x)&true --> x::node<val_23_781,next_23_782>@M * (HP_783(next_23_782))&true,
 (HP_783(res)) * x::node<val_23_781,res>@M&
   XPURE(HP_786(next_23_782)) --> G(x,res)&true]

When I trace with -dd, I got a surprising do_match:

!!!ll-getnext.ss:20: 8: [entail:20][post:20]do_match: using  G(x,res) to prove  G(x,res)
!!!ll-getnext.ss:20: 8: [entail:20][post:20]do_match: source LHS:  es_formula: HP_783(next_23_782)&next_23_782=res&{FLOW,(22,23)=__norm}[]

which led to:
                   (HP_783(res)) * x::node<val_23_781,res>@M&
                     XPURE(HP_786(next_23_782)) --> G(x,res)&true]

and also a residue:
 es_formula: HP_783(next_23_782)&next_23_782=res&{FLOW,(22,23)=__norm}[]

This is also reflected in sleek-logging:

 id: 6; caller: []; line: 20; classic: false; kind: POST; hec_num: 5; evars: []; c_heap: emp
 checkentail (HP_783(next_23_782)) * x::node<val_23_781,next_23_782>@M[Orig]&
next_23_782=res&{FLOW,(22,23)=__norm}[]
 |-  G(x,res)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ (HP_783(res)) * x::node<val_23_781,res>@M&
   XPURE(HP_786(next_23_782)) --> G(x,res)&true]
res:  [
  HP_783(next_23_782)&next_23_782=res&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [x]
  ]

*/




