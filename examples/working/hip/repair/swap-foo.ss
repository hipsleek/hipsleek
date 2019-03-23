data node {
   int val;
}

// HeapPred P(node x,node y).
// HeapPred Q(node x,node y).

// void foo(node x, node y)
//   requires P(x,y) ensures Q(x,y);

void swap(node x, node y)
  requires x::node<a> * y::node<b>
  ensures x::node<b> * y::node<a>;
{
  // x::node<a> * y::node<b>
  int t = x.val;
  // x::node<a> * y::node<b> & t = a |- P(x,y)
  // -> choose P(x,y) = x::node<a> * y::node<b> & t = a
  // -> x::node<a> * y::node<b> & t = a |- x::node<a> * y::node<b> & t = a
  // match (x,x) (y, y) -> t = a |- t = a
  // residue emp & t=a
  // foo(x,y);   // need to synthesize foo(x,y)
  x.val = y.val;
  //Q(x,y) & t=a
  // Q(x,y) & t=a |- exists k. y::node<k>
  //++++ (1)  Q(x,y) = exists k. y -> node<k> * Q'(x,y)
  // exists k. y -> node<k> * Q'(x,y) & t = a |- exists k. y -> node<k>
  // --> Q'(x,y) & t = a
  y.val = t;
  // y-> node<t> * Q'(x,y) & t = a |- x::node<b> * y::node<a>
  // <-> Q'(x,y) & t =a |- x::node<b>
  // -> choose Q'(x,y) = x::node<b>
  // -> Q(x,y) = exists k. y -> node<k> * x->node<b>
  // -> {x::node<a> * y::node<b> & t = a} fcode(x,y) {exists k.y-> node<k> * x->node<b>}
  // x::node<b> * y::node<a>
}
// x::node<a> * y ::node<b> & t = a
// x.val = y.val
// x::node<b> * y::node<val_11> 

/* Round 1: original constraints

  x::node<a> * y::node<b> & t=a |- P(x,y) ~> R(x,y,a,b)
  R(x,y,a,b) * Q(x,y) & t=a |- exists k. y::node<k>   ~> T(x,y,a,b)
  T(x,y,a,b) * y::node<t> & t=a |- x::node<b> * y::node<a>  ~> emp.
*/

/* Round 2: classic entailments with empty residue

  x::node<a> * y::node<b> & t=a |- P(x,y) * R(x,y,a,b)
  R(x,y,a,b) * Q(x,y) & t=a |- exists k. y::node<k> * T(x,y,a,b)
  T(x,y,a,b) * y::node<t> & t=a |- x::node<b> * y::node<a>
*/

/* Round 3: finding T(x,y,a,b)

  x::node<a> * y::node<b> & t=a |- P(x,y) * R(x,y,a,b)
  R(x,y,a,b) * Q(x,y) & t=a |- exists k. y::node<k> * T(x,y,a,b)
  T(x,y,a,b) |- x::node<b>   ==>  solution: T(x,y,a,b) := x::node<b>
*/ 

/* Round 3: replace T(x,y,a,b) by its solution

  x::node<a> * y::node<b> & t=a |- P(x,y) * R(x,y,a,b)
  R(x,y,a,b) * Q(x,y) & t=a |- exists k. y::node<k> * x::node<b>

  Heuristics: P(x,y), Q(x,y) are specification, and they should be
  as big as possible.
*/

/* HIP-generated constraints
inp1:     y::node<b>@M * x'::node<a>@M&x'=x & y'=y & t'=a
inp2:     P(x',y')
residue:  T0(b,x',x,y',y,t',a)

inp1:     T0(b,x',x,y',y,t',a) * Q(x',y')
inp2:     exists val_31_1885'. y'::node<val_31_1885'>
residue:  T1(b,x,y,t',a,x',y')

inp1:     exists t': T1(b,x,y,t',a,x',y') * y'::node<t'>
inp2:     exists b_89,a_90: x::node<b_89>@M * y::node<a_90>@M&b_89=b & a_90=a
residue:  emp

*/