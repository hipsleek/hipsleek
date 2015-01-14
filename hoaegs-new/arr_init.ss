relation zeros(int[] a, int i, int j) == (i > j | forall ( k : (k < i | k > j | i <= k & k <= j & a[k] = 0))).

/* a and b are identical except a[k] = 0 for all i <= k <= j */ 
relation identicalzeroes(int[] a, int[] b, int i, int j) == forall ( k : (k < i & a[k] = b[k] | k > j & a[k] = b[k] | i <= k & k <= j & a[k] = 0)).

void zinit(int[]@R a, int i, int j) 
	requires [k,t] dom(a,k,t) & k <= i & j <= t
	ensures dom(a',k,t) & identicalzeroes(a',a,i,j);
{
	if (i <= j)
	{
/*		assume dom(a',k,t);*/
		a[i] = 0;
/*		assume dom(a',i+1,j);*/
		zinit(a,i+1,j);
	}
}

/*int main()
  requires true
  ensures res = 1;
{
  int[] a;
  assume a' = a & dom(a',0,5);
  zinit(a,3,5);
  assert identicalzeroes(a',a,3,5);
  return 1;
}*/
