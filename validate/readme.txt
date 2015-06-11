Implemented feature
===================
We introduce a new feature to test for sleek inference capability.
Currently, we can check for infer heap/pure and also residue,
but not relational assumptions yet.

A sample file is in ex4f.slk

The new commands are to come immediately after
an entailment, but before the next. You may start
writing them in sleek files, and we will be supporting
these in run-fast-test in future.

Some examples:

# ex4f.slk

checkentail x::node<aaa,q>*q::node<aaa,null> |- emp.
print residue.
expect Valid.
// below is for checking residues.
expect_infer Valid R{x::node<bb,q>*q::node<bb,null>}. //Valid 1
expect_infer Valid R{x::node<bb,q>*q::node<bb,_>}.//Valid
expect_infer Valid R{x::node<bb,q1>*q1::node<bb,_>}.//Valid
expect_infer Fail R{x::node<bb,q>*q::node<bb+1,_>}. //Invalid
expect_infer Valid R{x::node<bb,_>*qq::node<bb,_>}. //Invalid
expect_infer Valid R{x::node<bb,_>*q::node<bb,_>}. //Valid??

# ex5a.slk

infer [n] y=null |- y::ll<n>.  
print residue.
expect_infer Fail I{y=null}.
expect_infer Valid I{n=0}.


====================================

We need to validate SLEEK's inference capability
including implicit instantiation for residue.

Given:
  infer [..] LHS |- RHS.

SLEEK will return a number of things:
 (i) residues 
 (ii) pre-condition in several forms:
       (a) heap
       (b) pure
       (c) relational assumption/definitions
       (d) shape assumption/definitions
Residue is in a set of states while, pre-conditions
are attached to each such state.

As state-of-state is a proof search, we intend that
check that one such state has the residue and
inferred pre-conditions.

Let us assume that a residue R and a precondition P
is generated. Let us also assume that we
are expecting exp_pre and exp_post.

 expect_infer I{exp_pre} R{exp_post}

We must then check the following:

      Xpure(Consume) !=false
 -------------------------------
 R & Xpure(Consume) & exp_pre |- P            (1)


      Xpure(LHS) !=false
 ---------------------------------------
 XPure(LHS) & P               |- exp_pre      (2)

      Xpure(Consume) !=false
 -------------------------------
 R & Xpure(Consume) |- exp_post               (3)

This will help use ensure that pre-cond
inferred is precise, and that residue
is stronger than our expectation.

For pre-cond inferred, we usually expect
(2) to hold so that we know that P is
at least as strong as exp_pre. However, occasiionally
we also like to infer some weakest pre,
so we will also impose (1).

For inferred residue, we may also wish for
a residue that is not too strong, as it could be
a source of unsoundness; so we may also have:
 
      Xpure(Consume) !=false
 -------------------------------
 exp_post & Xpure(Consume) |- P               (4)

For equivalence proving, I suggest we use:
 expect_infer IE{exp_pre} RE{exp_post}
