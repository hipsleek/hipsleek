/**
 * Find the sum of the elements of an array. This examples
 * show two ways of computing the sum and illustrates the use
 * of induction.
 * 
 * @author Vu An Hoa
 */

relation sumarray(int[] a, int i, int j, int s) == 
	(i > j & s = 0 | i = j & s = a[i] | i < j & sumarray(a,i+1,j,s-a[i])).

axiom i < j & sumarray(a,i,j-1,s-a[j]) ==> sumarray(a, i, j, s).

//relation sumarray(int[] a, int i, int j, int s) == 
//	(i > j & s = 0 | i = j & s = a[i] | i < j & sumarray(a,i,j-1,s-a[j])).

int sigmaright(int[] a, int i, int j) 
	case {
		i <= j ->  
				requires dom(a,i,j) & Term[j-i] /* the allocation is from a[i..j] */
				ensures sumarray(a,i,j,res);
		i > j -> 
				requires Term
			  ensures sumarray(a,i,j,res);
	}
{
	if (i > j)
		return 0;
	else 
		return a[i] + sigmaright(a, i+1, j);
}

int sigmaleft(int[] a, int i, int j) 
	requires [t,k] dom(a,t,k) & t <= i & j <= k
	ensures sumarray(a,i,j,res);
{
	if (i > j)
		return 0;
	else 
		return sigmaleft(a, i, j-1) + a[j];
}

void test()
	requires true
	ensures true;
{
	int x = 0;	
}
