/*
  prim pred can have an output compatible type
  need to support boolean operators, like 
    | or &

*/

pred_prim /* int */ ann<n:int,b:bool>;
// need to support output type of primitive predicate

bool eqInt(int x, int y)
  requires x::ann<i,a1>@L * y::ann<j,a2>@L
//ensures  res = (i>j);
  ensures  res = (i=j);
  //ensures  res & i=j | !res & !(i=j);

/*
# ex-3.ss

parser error:

  ensures  res = (i=j);

 File "ex-3.ss", line 13, characters 21-22
 --error: Failure("with 2 convert bexpr  1")

  ensures  res = (i>j);
 File "ex-3.ss", line 13, characters 21-22
 --error: Failure("with 2 convert bexpr  1")
  
*/
