void loop ()
  requires Loop
  ensures false;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return;
  else {
    loop();
    f(x + 1);
  }
}

/*
# loop-2.ss

Temporal Assumptions:
 termAssume x'<=0 & x'=x & v_bool_10_1126' & x'<=0 & 
v_bool_10_1126' --> fpost_1122(x).

 termAssume 0<x' & x'=x & !(v_bool_10_1126') & 0<x' & 
!(v_bool_10_1126') & fpre_0(x) --> Loop.

2 missing relations:
  - pre of f
  - post of else_branch


Base/Rec Case Splitting:
[	f: [[2] x<=0@B]
]
Termination Inference Result:
f:  case {
  x<=0 -> requires emp & Term[30,1]
 ensures emp & true; 
  }

*/
