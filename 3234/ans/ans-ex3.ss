int minf(int i, int j)  
  requires true
  ensures res=min(i,j);
  requires true
  ensures i<=j & res=i or i>=j & res=j;
{
	if (i<j) return i;
	else return j;
}

int maxf(int i, int j)  
  requires true
  ensures res=max(i,j);
  requires true
  ensures i<=j & res=j or i>=j & res=i;
{
	if (i>j) return i;
	else return j;
}
