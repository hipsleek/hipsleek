int sum_tail(int i, int n) 
 case {
    i<=0 -> ensures res=n;
    i>0  -> ensures res=i+n;
  }
{
	if (i<=0) return n;
	else return sum_tail(i-1,1+n);
}
