// (i) Add Term criterion with ranking function for the recursive case
// (ii) Add a strongest possible postcondition for the recursive case
//      and use -tp redlog to perform the verification

int sum_down(int i) 
case {
  i<=0 -> requires Term
          ensures res=0;
  i>0 -> requires true
         ensures res>=n;  
}
{
	if (i>0) return i+sum_down(i-1);
	else return 0;
}
