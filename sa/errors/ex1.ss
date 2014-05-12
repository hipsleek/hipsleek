
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

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;

  /*
H1<> == self::node<_,p> & p=null
	or self::node<_, q> * q::H1<>
	inv true;
*/
HeapPred H(node a).
HeapPred H1(node a).
HeapPred G(node a, node b).
HeapPred HP_537(node a, node b).
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
   bool b;
   x = x.next;
   b = x!=null;
   if (b) {
     //   dprint;
     foo(x);
   }
 }

/*

*************************************
*******relational assumptions ********
*************************************
[ // BIND
(0)H(x)&true --> x::node<val,next>@M * HP_939(next)&true,
 // PRE_REC
(1;0)HP_939(next)&next!=null --> H(next)&true,
 // POST
(1;0)x::node<val,next>@M * H1(next)&next!=null --> H1(x)&true,
 // POST
(2;0)x::node<val,next>@M * HP_939(next)&next=null --> H1(x)&true
]

 */
