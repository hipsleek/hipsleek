data node {
  node next;
}

ll<> == self = null
	or self::node<q> * q::ll<>
  inv true;

infll<> == self::node<q>*q::infll<>
  inv self!=null;

HeapPred H1(node a).
HeapPred G1(node b, node c).

bool randB()
requires true
ensures res or !res;

int loop(ref node ptr)
   requires ptr::infll<>
   ensures ptr'::infll<> ;//'
   requires ptr::ll<>
   ensures ptr'::ll<> ;//'
/*
  infer[H1,G1]
  requires H1(ptr)
  ensures G1(ptr',ptr); //'
*/

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
# ll-back-3.ss

// PRE_REC
H1(ptr) * tmp_31'::node<ptr>@M --> H1(tmp_31'),
 // POST
H1(ptr)& ptr=ptr' --> G1(ptr',ptr),
 // POST
G1(ptr',tmp_903) --> G1(ptr',ptr)]

This is similar to ll-back-1.ss.

We first attempt to deal with pre-H1, and is
immediately saddled with a pre-obligation of the form:

  H1(ptr) * tmp_31'::node<ptr>@M --> H1(tmp_31'),

As H1 is not yet defined, we cannot perform a pre-obligation
proving task. Instead, we use this relation to form a
defn of the form:

 H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr)

If we freeze at this point, we may obtain a pre-condition
that is too strong as it is an infinite list. Thus, we
choose to weaken it further to:

 H1(tmp_31') <--  tmp_31'::node<ptr> * H1(ptr)
                  or tmp_31'=null

(We need to tighten the above reasoning.)

Once, we have a defn for H1:

 H1(tmp_31') <->  tmp_31'::node<ptr> * H1(ptr)
                  or tmp_31'=null

The synthesis for G is more straightforward, as we will
have:

(1;0)H1(ptr)& ptr=ptr' --> G1(ptr',ptr),
(2;0)G1(ptr',tmp_903) --> G1(ptr',ptr)]

which is used to form:

  H1(ptr)& ptr=ptr' \/  G1(ptr',tmp_903) --> G1(ptr',ptr)]

Applying a fix-point analysis then gives:

  H1(ptr') --> G1(ptr',ptr)]

which can now be approximated by:
  
  G1(ptr',_) == H1(ptr')

(* FIXPOINT analysis is a bit new here but is a general
   mechanism for dealing with recursion *)


*/

