pred_prim nondet<>
  inv true;

bool nondeterm()
  requires true
  ensures res::nondet<>;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures emp;
    i >=0 -> requires LoopND ensures emp;
  }
{ 
  bool b = nondetermB(); // b'::nondet<>
  bool d = i>=0 && b;   // d'= i'>=0 && b'
  if (d) {
    foo(i-1);
    dprint;
  }
}

/*
# nondet/ex6-nd-term.ss

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures emp;
    i >=0 -> requires LoopND ensures emp;
  }
{ 
  bool b = nondetermB(); // b'::nondet<>
  bool d = i>=0 && b;   // d'= i'>=0 && b'
  if (d) {
    foo(i-1);
    dprint;
  }
}

Above spec would fail, as d' is not NONDET.
This is so, as i>=0 is DET. If i>=0 had been false,
the conditional becomes deterministically FALSE.
Hence, the conditional here is not non-deterministic.

ND /\ ND --> ND
!ND --> ND
ND+c --> ND
ND*n & n!=0 --> ND
ND --> ND
ND=c --> ND

Definition: A test t is non-determ under a state, S,
if the following conditions hold:

   not(S |- t) /\ not(S |- !t)  /\  S |- t::nondet<>

We may get nested conditionals (or nested case-spec),
and their reasoning would have to be done as follows.

Let ND denotes non-deterministic test,while D denotes 
deterministic test. Let S1, S2 and S3 be the final
states of the three branches.

   if ND then
      if D then S1 (ND1)
      else S2 (ND1)
   else S3 (ND2)

Based on the conditional flow, we require the
following check for Looping test.

  LoopRet(S3) \/ (LoopRet (S1) /\ LoopRet(S2) 

  LoopRet(S) means 
    if (LoopND \in S) | Loop \in S then unreachable.
*/
