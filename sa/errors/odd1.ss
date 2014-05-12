
data node {
  int val;
  node next;
}
/*
H<> == self::node<_,p> * p::ll<>
  inv true;
*/
ll<> == self=null
	or self::node<_, q> * q::ll<> & self!=null
	inv true;


HeapPred H(node a).
HeapPred H1(node a).

void foo(node x)

 infer [H,H1]
 requires H(x)
 ensures  H1(x);

/*
  requires x::H<>
  ensures x::H1<>;
*/
/*
 case {
   x=null -> ensures true & flow __Error;
   x!=null -> requires x::node<_,p> * p::ll<>
     ensures x::node<_,p> * p::ll<>;
 }
*/
 {
   if (x.next !=null) {
     //   dprint;
     foo(x.next.next);
   }
 }

/*

[ // BIND
(0)H(x)&true --> x::node<val,next>@M * HP_933(next)&
true,
 // BIND
(1;0)HP_933(next)&next!=null --> next::node<val,next1>@M * HP_948(next1)&
true,
 // PRE_REC
(1;0)HP_948(next)&true --> H(next)&
true,
 // POST
(1;0)x::node<val,next>@M * next::node<val1,next1>@M * H1(next1)&
true --> H1(x)&
true,
 // POST
(2;0)x::node<val,next>@M * HP_933(next)&next=null --> H1(x)&
true]

 */
