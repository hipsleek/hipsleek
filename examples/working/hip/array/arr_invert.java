/**
 Problem 2 in VSComp 2010: Inverting an Injection
 @author Vu An Hoa
 @date 24/06/2011
 **/

relation dom(int[] a, int i, int j) == true.

// b[-infty..infty] is a left inverse of a|{i..j}
// i.e. b \circ a (x) = x for all x in {i..j}
relation IsLeftInverse(int[] a, int[] b, int i, int j) ==
	forall(k : (k < i | k > j | b[a[k]] = k)).

relation IsInjective(int[] a, int i, int j) ==
	forall(x,y : (x < i | x > j | y < i | y > j | x = y | a[x] != a[y])).

// a[i..j] is a permutation of [l..h]
relation Permute(int[] a, int i, int j, int l, int h) ==
	forall(k : (k < i | k > j | l <= a[k] & a[k] <= h)) & // range of values
	forall(u : u < l | u > h | ex(v: i <= v <= j & a[v] = u)) & // surjectivity
	IsInjective(a,i,j). // injectivity


// Construct inverse of a|{0..n-1} provided 
// (i)	range(a) = {0..n-1}
// (ii)	a is injective
// i.e. a|{0..n-1} is a permutation of (0,1,...,n-1)
void Invert(int[] a, ref int[] b, int n)
	requires dom(a,0,n-1) & dom(b,0,n-1) & Permute(a,0,n-1,0,n-1)
	ensures IsLeftInverse(a,b',0,n-1) & IsInjective(b',0,n-1); 
{
	// for(int i = 0; i < n; i++) b[a[i]] = i // equivalent iterative code
	InvertHelper(a,b,n,0);
}

// Tail recursive expansion of the loop
void InvertHelper(int[] a, ref int[] b, int n, int i)
	requires 	dom(a,0,n-1) & dom(b,0,n-1)
			 	& Permute(a,0,n-1,0,n-1)
				& IsLeftInverse(a,b,0,i-1)
	ensures 	IsLeftInverse(a,b',0,n-1);
{
	if (i < n) {
		b[a[i]] = i;
//		assert IsLeftInverse(a,b',0,i);
		InvertHelper(a,b,n,i+1);
	}
}
