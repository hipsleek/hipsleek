data node{
	node next;
}

HeapPred P(node a).
HeapPred G(node a).

void loop (node x)
  infer [P,G]  requires P(x)  ensures  G(x);
  //requires x::node<_> ensures false;
{
   node y = x.next;
   loop(x);
}

/*
loop-3.ss
=========
GOT
===
[P(x) --> x::node<next_16_901>@M * H_2(next_16_901).
 H_2(next_16_901) * 
  x::node<next_16_901>@M |#| x::node<next_16_901>@M --> P(x).
G(x) --> G(x).
--------------------
 P(x_906) ::= x_906::node<next_16_901>@M * H_2(next_16_901),
 G(x_907) ::= G(x_907),
 H_2(next_16_901) ::= NONE]

Some issues:
------------
(1) we do not need a guard below. Why was it formed?
 H_2(next_16_901) * 
  x::node<next_16_901>@M |#| x::node<next_16_901>@M --> P(x).

(2) Whenever we have:
      x::node<n>*H_2(_) --> P(x)
   We regard this as a pre-obligation which we will perform after
   P(x) has been synthesized.

 Is that a pre-obligation (obligation for pre) that needs to be checked.
  x::node<n> |- P(x)
 based on the definition of P(x) that was derived.

*/

