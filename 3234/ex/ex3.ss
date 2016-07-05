
// (i) write stronger postcondition for the two methods
//     below. You may use min(?,?) or max(?,?).
// (ii) write stronger postcondition without using min/max
//     but use instead "or" operator.


int minf(int i, int j)  
  requires true
  ensures res=i or res=j;
{
	if (i<j) return i;
	else return j;
}

int maxf(int i, int j)  
  requires true
  ensures res=i or res=j;
{
	if (i>j) return i;
	else return j;
}
