UTPre@f fpre(int x).
UTPost@f fpost().

int fact(int x)
  infer [@term]
  case {
    x = 0 -> requires Term[] ensures res>=1 & fpost();
    x != 0 -> requires fpre(x) ensures res>=1 & fpost();
  }

{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}

/*
# fact2b.ss

why give printing when no termination inference
or verification is requested?

*************************
* TERMINATION INFERENCE *
*************************
Temporal Assumptions:

Base/Rec Case Splitting:
[]
Termination Inference Result:

Termination checking result: SUCCESS

*/
