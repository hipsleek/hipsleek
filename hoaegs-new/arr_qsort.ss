/**
 Example: Quicksort
 **/

relation dom(int[] a, int low, int high) == (dom(a,low-1,high) | dom(a,low,high+1)).

relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j  | i<j & forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

relation strupperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] < s))).

relation strlowerbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] > s))).

relation alleqs(int[] a, int i, int j, int s) == (i > j | i<=j & forall ( k : (k < i | k > j | a[k] = s))).

relation upperbndprev(int[] a, int[] b) == forall(i,j,s : (!(strupperbnd(a,i,j,s)) | strupperbnd(b,i,j,s))).

relation lowerbndprev(int[] a, int[] b) == forall(i,j,s : (!(strlowerbnd(a,i,j,s)) | strlowerbnd(b,i,j,s))).

relation bnd(int[] a, int i, int j, int low, int high) == (i > j | i<=j & forall ( k : (k < i | k > j | low <= a[k] <= high))).

relation matchinp(int x, int y) == true.

void arraypart(ref int[] a, int i, int j, int x, ref int k, ref int t)
	case {
		i > j  -> ensures k' = i - 1 & t' = j + 1 & a' = a;
		i <= j -> requires [u,v,l,h] dom(a,u,v) & u<=i & j<=v 
					& matchinp(l,h) & bnd(a,i,j,l,h)
                  ensures dom(a',u,v) & i - 1 <= k'  & k' <= j & bnd(a', i, k', l,x-1) 
                  & alleqs(a', k'+1, t'-1, x) & i <= t' & t' <= j + 1 
                  & bnd(a', t', j, x+1,h) & idexc(a', a, i, j) & bnd(a',i,j,l,h);
	}
{
	if (i > j) {
		k = i - 1;
		t = j + 1;
	}
	else {
		if (a[i] < x) {
			arraypart(a, i + 1, j, x, k, t);
		}
		else if (a[i] > x) {
			int temp = a[i];
			a[i] = a[j];
			a[j] = temp;
			arraypart(a, i, j - 1, x, k, t);
		}
		else {
			arraypart(a, i + 1, j, x, k, t);
			a[i] = a[k];
			a[k] = x;
			k = k - 1;
		}
	}
}

void qsort(ref int[] a, int i, int j)
	case {
		i >= j -> ensures a=a';
        i < j -> requires [u,v,l,h] dom(a,u,v) & u<=i & j<=v & bnd(a,i,j,l,h)
          ensures dom(a',u,v) & bnd(a',i,j,l,h) & sorted(a',i,j) & idexc(a',a,i,j);
    }
{
	if (i < j)
	{
		int k, t;
        int x = a[i];
		arraypart(a, i, j, x, k, t);
		qsort(a, i, k);
		assume bnd(a',t',j,x'+1,h);
		qsort(a, t, j);
		assume bnd(a',i,j,l,h);
	}
}
