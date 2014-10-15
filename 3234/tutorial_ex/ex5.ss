int sum_up(int i, int n) 
  requires n>=i>=0
  ensures res>=i;
{
	if (i==n) return i;
	else return i+sum_up(i+1,n);
}
