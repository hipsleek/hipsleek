data node{
	node next;
}

HeapPred P(node a).
HeapPred G(node a).

foo<> == self::node<q>*q::foo<> inv self!=null;
void loop (node x)
infer [P,G]  requires P(x)  ensures  G(x);
//  requires x::foo<> ensures x::foo<>;
{
   node y = x.next;
   loop(y);
}

/*
# loop-4.ss

(minor)

GOT
===
 P(x) --> x::node<next_1>@M * H_2(next_1),
 H_2(next_1) --> P(next_1),
 x::node<next_1>@M * G(next_1) --> G(x)]
--------------------
[P(x_906) ::= x_906::node<next_1>@M * H_2(next_1),
 G(x_908) ::= x_908::node<next_1>@M * G(next_1),
 H_2(next_7) ::= P(next_7)]

EXPECTING
=========
[P(x_906) ::= x_906::node<next_1>@M * P(next_1),
 G(x_908) ::= x_908::node<next_1>@M * G(next_1),
]

ALGO
====
We have two pre-predicates:
 P(x) --> x::node<next_1>@M * H_2(next_1),
 H_2(next_1) --> P(next_1),

H_2(..) is simpler than P(..)

Step 1
======
transform and confirm H_2.
 H_2(next_1) --> P(next_1),
 H_2(next_1) <-> P(next_1),


Step 2
======
transform and confirm P.
 P(x_906) ::= x_906::node<next_1>@M * H_2(next_1),
 // unfold H_2 which has a simple RHS
 P(x_906) ::= x_906::node<next_1>@M * P(next_1),


*/

