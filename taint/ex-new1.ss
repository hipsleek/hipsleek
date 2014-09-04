/*
  prim pred can have an output compatible type
  need to support boolean operators, like 
    | or &

*/

pred_prim /* int */ ann<n:int,b:bool>;
// need to support output type of primitive predicate


int add(int x, int y) 
  requires x::ann<i,a>@L*y::ann<j,b>@L
  //ensures  res::ann<i+j,r> & r = (a|b);
  ensures  res::ann<i+j,a|b>;
// need to support boolean operator

/*

ERROR: at ex-new1.ss_15:24_15:27 
Message: expected cexp, found pure_constr
 File "ex-new1.ss", line 15, characters 26-27
 --error: Failure("expected cexp, found pure_constr")
 at:(Program not linked with -g, cannot print stack backtrace)
caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("expected cexp, found pure_constr")
Error3(s) detected at main 
*/
