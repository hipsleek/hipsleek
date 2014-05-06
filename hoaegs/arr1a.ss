/**
 Example: array initialization.
 **/
 
relation zero(int[] a, int[] na, int i) == 
  forall(j: j=i & na[j] = 0 | j!=i & na[j] = a[j] ).

void test(int[]@R a, int i) 
	requires true
  ensures zero(a,a',i);
{
		a[i] = 0;
}

