data node {
  node next;
}

HeapPred UNK(node a).

ls<p> == self = p
  or self::node<q>* q::ls<p>;

cll<> == self::node<q> * q::ls<self>
  inv self!=null;

ll<> == self = null
	or self::node<q> * q::ll<>
  inv true;

infll<> == self::node<q>*q::infll<>
  inv self!=null;

lasso<> == self::node<q>*q::lasso<>
      or self::cll<>
  inv self!=null; 

lasso2<> == self::node<q>*q::lasso2<>
      or UNK(self)
  inv true; 

HeapPred H1(node a).
HeapPred G1(node b, node c).

bool randB()
requires true
ensures res or !res;

int loop(ref node ptr)
/*
   requires ptr::infll<>
   ensures ptr'::infll<> ;//'
   requires ptr::ll<>
   ensures ptr'::ll<> ;//'

   requires ptr::lasso2<>
   ensures ptr'::lasso2<> ;//'
*/

  infer[H1,G1]
  requires H1(ptr)
  ensures G1(ptr',ptr); //'


{
  if (randB()) {
    return -1;
  }
  node tmp = new node(ptr);
  ptr = tmp;
  loop(ptr);
  return 0;
}

/*
# ll-back-4.ss

The above code verifies in default.

// PRE_REC
H1(ptr) * tmp_31'::node<ptr>@M --> H1(tmp_31'),
 // POST
H1(ptr)& ptr=ptr' --> G1(ptr',ptr),
 // POST
G1(ptr',tmp_903) --> G1(ptr',ptr)]

This example is similar to ll-back-1.ss.

We first attempt to deal with relational assumption of H1,
and is immediately saddled with a pre-obligation of the form:

  H1(ptr) * tmp_31'::node<ptr>@M --> H1(tmp_31'),

As H1 is not yet defined, we cannot perform a pre-obligation
proving task. Instead, we use this relation to form a
defn of the form:

 H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr)

If we freeze at this point, we may obtain a pre-condition
that is too strong as it is an infinite list. Thus, we
choose to weaken it further by applying a (greatest) fixpoint
computation technique. with an unknown predicate:

 H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr)
                  or UNK(tmp_31')

How is this weakening applied? For least fixed point, we start
with false, and progressively weaken to a fix-point.

fix rules = \{ H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr) \}

For greatest fix-point, we start with:
//  H1(tmp) <- UNK(tmp)
//0
H1(tmp) <- HTrue & true

and then strengthen = apply fix to the current set + weaken (widening)
 by disjunction to:
//1
 H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr)
                  or UNK(tmp_31')
//2
H1(tmp_31') <--  tmp_31'::node<ptr> * ptr::node<ptr1> * H1(ptr1)
                 tmp_31'::node<ptr> * H1(ptr)
                  or UNK(tmp_31')

normalize (extract recurrence points):
H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr)
                  or UNK(tmp_31')

==> fixpoint
(PS We need to formalise this weakening and
fix-point process)

Assume:

  UNK(t) --> H1(t) 

Add:
  t::node<p> * H1(p) --> H(t)

Result:
  UNK(t)
  or t::node<p>* H1(p) --> H1(t)


This weakening is general and would cover both ll and
lasso-like structure. In addition, it can also be
verified by our system (under default branch).

The synthesis for G is more straightforward, as we will
have:

H1(ptr)& ptr=ptr' --> G1(ptr',ptr),
G1(ptr',tmp_903) --> G1(ptr',ptr)]

which is used to form:

  H1(ptr)& ptr=ptr' \/  G1(ptr',tmp_903) --> G1(ptr',ptr)]

We can apply a least fixed-point technque to G, as follows.
First, assume false --> G(_,_). 

In 2nd iteration:

  H1(ptr)& ptr=ptr' \/  false --> G1(ptr',ptr)]
  H1(ptr)& ptr=ptr' --> G1(ptr',ptr)]

In 3rd iteration:

  H1(ptr)& ptr=ptr' \/  G1(ptr',tmp_903) --> G1(ptr',ptr)]
  H1(ptr)& ptr=ptr' \/  H1(tmp_903) & tmp_903=ptr' --> G1(ptr',ptr)]
  H1(ptr)& ptr=ptr' \/  H1(ptr') & true --> G1(ptr',ptr)]
  H1(ptr') & (ptr'=ptr | true) --> G1(ptr',ptr)]
  H1(ptr')  --> G1(ptr',ptr)]

In 4th iteration:

  H1(ptr)& ptr=ptr' \/  H1(ptr') --> G1(ptr',ptr)]
  H1(ptr') --> G1(ptr',ptr)]

Thus, the strongest post-cond is:

  H1(ptr') --> G1(ptr',ptr)]

which can now be used to define a new post-pred:
  
  G1(ptr',_) == H1(ptr')


*/

