// (i) Provide a ranking function that guarantees total correctness
// (ii) Write a stronger postcondition involving [res,i,n]
//      of the form 2*res=..
//   Use -tp redlog for your verification


int sum_up(int i, int n) 
  requires n>=i>=0 & Term[n-i]
  ensures 2*res+(i*(i-1))=n*(n+1);
{
	if (i==n) return i;
	else return i+sum_up(i+1,n);
}
