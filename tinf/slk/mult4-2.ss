bool nondet ()
  requires Term
  ensures true;
  
void f(int x,bool bbb)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (bbb) f(x - 1,bbb);
    else f(x + 1,bbb);
  }
}
  
/*
# mult4-2.ss

--print-dis-tidy --esl 

why only one termAssume logged?

tntrel_ass: [@Call:  
termAssume 0<=x' & b=b' & x=x' & !(v_bool_10_876') & 0<=x' & 
!(v_bool_10_876') & b' & x'=v_int_12_873'+1 & fpre_0(x,b) 
--> fpre_0(v_int_12_873',b').]

 termAssume 0<=x' & b=b' & x=x' & !(v_bool_10_876') & 0<=x' & 
!(v_bool_10_876') & b' & x'=v_int_12_873'+
1 & fpre_0(x,b) --> fpre_0(v_int_12_873',b').

Why did we change b to b>=1 in termination inference analysis?

Termination Inference Result:
f:  case {
  0<=x & 1<=b -> requires emp & MayLoop[]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Term[30,1]
 ensures emp & true; 
  b<=0 & 0<=x -> requires emp & MayLoop[]
 ensures emp & true; 

our case-analysis don't work with boolean?

Expect one Loop and one Term..

*/
