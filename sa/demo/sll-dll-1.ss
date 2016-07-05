data node{
//        int val;
        node prev;
        node next;
}


ll<> == self = null  or self::node< _ , q> * q::ll<>;
dll<p> == self = null or self::node< p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node b).
// seems critical to have @NI
PostPred G1(node a, node b).

void paper_fix (node x, node p)
infer[H1,G1] requires H1(x,p) ensures G1(x,p);
//requires x::ll<> ensures x::dll<p>;
{
        if (x!=null) 
        {
            x.prev=p;
	        paper_fix(x.next,x); 
        }
}

/*
 with #
[ // BIND
(1;0)H1(x,p@NI)&x!=null --> x::node<prev_21_891,next_21_892>@M *
HP_893(prev_21_891,p@NI) *
HP_894(next_21_892,p@NI),
 // PRE_REC
(1;0)HP_894(next_21_892,p@NI) |#| x'::node<p,next_21_892>@M --> H1(next_21_892,x'@NI),
 // POST
(1;0)x::node<p,next_21_892>@M *
G1(next_21_892,x) --> G1(x,p),
 // POST
(2;0)H1(x,p@NI)&
x=null --> G1(x,p)]

*************************************
*******relational definition ********
*************************************
[ G1(x_912,p_913) ::=
 emp&x_912=null
 or x_912::node<p_913,next_21_892>@M * G1(next_21_892,x_912)
 ,
 H1(x_910,p_911) ::=
 emp&x_910=null
 or H1(next_21_907,x_910) * x_910::node<prev_21_906,next_21_907>@M *
    HP_893(prev_21_906,p_911)
 ,
 HP_893(prev_21_891,p) ::= NONE]

===============
without #
[ // BIND
(1;0)H1(x,p)&x!=null --> x::node<prev_21_891,next_21_892>@M *
HP_893(prev_21_891,p@NI) * HP_894(next_21_892,p@NI) *
HP_895(p,x@NI),
 // PRE_REC
(1;0)HP_894(next_21_892,p@NI) * HP_895(p,x@NI) *
x::node<p,next_21_892>@M --> H1(next_21_892,x),
 // POST
(1;0)G1(next_21_892,x)&
x!=null --> G1(x,p),
 // POST
(2;0)H1(x,p)&
x=null --> G1(x,p)]

*************************************
*******relational definition ********
*************************************
[ G1(x,p) ::=
 emp&x=null
 or emp&x!=null
 ,
 H1(x_905,p_906) ::=
 emp&x_905=null
 or x_905::node<prev_21_891,next_21_892>@M * HP_893(prev_21_891,p_906) *
    HP_894(next_21_892,p_906) * HP_895(p_906,x_905)
 ,
 HP_893(prev_21_891,p) ::= NONE,
 HP_895(p,x) ::= NONE]

*/
