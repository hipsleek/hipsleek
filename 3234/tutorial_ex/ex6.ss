// Write the strongest postconditions over [res,i,n]
// for the method below.

int sum_tail(int i, int n) 
 case {
    i<=0 -> ensures true;
    i>0  -> ensures true;
  }
{
	if (i<=0) return n;
	else return sum_tail(i-1,1+n);
}
