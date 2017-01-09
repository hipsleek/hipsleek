/*
  General high-order primitives for threads.

  Protocol: init --create()--> THRD --fork()--> THRD2 --join()--> DEAD
 */

//no need to define, already in prelude.ss
/* data thrd{ */
/* } */

//before fork
//P/Q : pre/post-conditions
pred_prim THRD{P,Q}<args>
inv true;

//after forked
//use different pred_prim
//to avoid join before fork
pred_prim THRD2{Q}<args>
inv true;

//after join
pred_prim DEAD<>
inv true;

//thread primitives look similar to channel primitive
//However, threads can be split and normalize

//this split lemma is already encoded into our system via @Split
//during entailment. Hence, can ignore?
lemma t::THRD2{%P * %Q}<args> -> t::THRD2{%P}<args> * t::THRD2{%Q}<args>;
//normalization
lemma t::THRD2{%P}<args> & t::DEAD<> -> %P;

// f(args) is a procedure with pre/post condition
// args is list of args
thrd create_thrd(proc f, list[] args)
  requires true
  ensures res::THRD{pre(f),post(f)}<args>;

void fork_thrd(thrd t)
  requires t::THRD{%P,%Q}<args> * %P
  ensures  t::THRD2{%Q}<args>;

void join_thrd(thrd t)
  requires t::THRD2{%Q}<args>
  ensures  t::DEAD<> * %Q;

