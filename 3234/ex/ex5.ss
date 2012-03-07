// (i) Add Term criterion with ranking function below
// (ii) Add a strongest possible postcondition for the recursive case
//      and use -tp redlog to perform the verification
// Hint:  result is i+(i+1)+...n

int sum_up(int i, int n) 
  requires n>=i>=0
  ensures res>=i;
{
	if (i==n) return i;
	else return i+sum_up(i+1,n);
}
