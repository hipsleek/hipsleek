relation P(int i, int pi, int r).

int fact(ref int i)
 infer [P]
 requires true
 ensures P(i,i',res);
{    
  if (i==0) return 1;
  else {
    int t=i;
    i=i-1;
    return t+fact(i);
  }
}

/*

 i>=0 & i'=0 & res>=1
 
 case {
   i<0 -> ensures false;
   i>=0 -> ensures res>=1 & i'=0;
 }


What is false?
  - non-termination
  - real bug?
  - possible bug?

*/
