void loop()
  requires Loop
  ensures false;

relation nondet_bool(bool b).
  relation nondet_int(bool i).

bool nondet()
  requires Term
  ensures true & nondet_bool(res);
  
void f(int x)
  infer [@term] requires true ensures true;
{
  if (x < 0) return;
  else {
    bool b = nondet();
    dprint;
    if (b)
      f(x + 1);
    else
      return;
  }
}

/*
# cex-3.ss

void f(int x)
  infer [@term] requires true ensures true;
{
  if (x < 0) return;
  else {
    bool b = nondet();
    if (b)
      f(x + 1);
    else
      return;
  }
}

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:emp&0<=x' & x'=x & !(v_bool_15_1380') & 0<=x' 
   & !(v_bool_15_1380') & nondet_bool(b_30')
    &{FLOW,(4,5)=__norm#E}[]
 ]

with det if:

Termination Inference Result:
f:  case {
  x<=(0-1) -> requires emp & Term[34,1]
     ensures emp & true; 
  0<=x -> requires emp & Loop{ 19:6}[]
     ensures false & false; 
  }

non-det if. Need to mark it as 
a possible MayLoop[ND] with a cex.

Termination Inference Result:
f:  case {
  x<=(0-1) -> requires emp & Term[34,1]
     ensures emp & true; 
  0<=x -> requires emp & MayLoop[]
     ensures emp & true; 
  }

*/
