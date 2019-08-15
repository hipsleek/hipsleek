data node {
   int val;
}

// HeapPred P(node x,node y).
// HeapPred Q(node x,node y).

// void fcode(node x, node y)
// requires P(x,y) ensures Q(x,y)
// ;

HeapPred P(node x).
HeapPred Q(node x).

void fcode(node x, node y)
requires P(x) ensures Q(x)
;

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
  // residue t = a
  fcode(x,y);

  //x.val = y.val;

  //Q(x,y) & t = a
  // Q(x,y) & t = a |- exists k. y -> node<k>
  // --> Q(x,y) = exists k. y -> node<k> * Q'(x,y)
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

// {exists k. y -> node<k>} y.val = t {y -> node<t>}

// Key observation: consider all as Hoare triple

// {(((int t;
// t = bind x to (val_24_1873) [read] in 
// val_24_1873);
// t = x.val

// {(int v_int_31_1875;
// (v_int_31_1875 = bind y to (val_31_1874) [read] in
// v75 = y.val
// val_31_1874;
// bind x to (val_31_1876) [write] in
// access x.val
// val_31_1876 = v_int_31_1875))});
// x.val = v75
// bind y to (val_37_1877) [write] in 
// val_37_1877 = t)}
// y.val = t
