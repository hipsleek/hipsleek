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
