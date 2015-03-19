/* Examples from Gulwani:PLDI08 */
void loop (int i, int even)
  infer [@term]
  requires true
  ensures true;
{
  if (i < 0) return;
  else if (even == 0) 
    loop(i-1, 1-even);
  else 
    loop(i+1, 1-even);
}
/*
Termination Inference Result:
loop:  case {
  i<=(0-1) -> requires emp & Term[61,1]
 ensures emp & true; 
  ((0<=i & 1<=even) | (even<=(i-1) & even<=0 & 
  0<=i)) -> requires emp & Loop[]
 ensures false & false; 
  even=0 & i=0 -> requires emp & Term[61,2]
 ensures emp & true; 
  }
*/
