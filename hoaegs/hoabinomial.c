// C(n,k) = number of ways to choose k objects from n objects
// Note: the definition below is applicable to all integers k
// and n, not just non-negative ones.
relation binom(int n, int k, int c) induction n, k.

axiom n >= 0 |- binom(n,0,1).

axiom n >= 0 & k = 0 & binom(n,k,c) |- c = 1.

axiom k > 0 |- binom(0,k,0).

axiom 0 < k & 0 < n & binom(n-1,k-1,c1) & binom(n-1,k,c2) |- binom(n,k,c1+c2).

axiom binom(n,k,c1) & binom(n,k,c2) |- c1 = c2.

//checkentail n >= 0 |- binom(n,n,1). 
//proof by induction:
//checkentail n = 0 |- binom(n,n,1).
//checkentail n > 0 & forall(m : m < 0 | m >= n | binom(m,m,1)) |- binom(n,n,1).

axiom n >= 0 |- binom(n,1,n).
//checkentail n >= 0 |- binom(n,1,n).
//proof by induction:
//checkentail n = 0 |- binom(n,1,n).
//checkentail n > 0 & forall(m : m < 0 | m >= n | binom(m,1,m)) |- binom(n,1,n).

//axiom 0 < k <= n & binom(n,k-1,c1) & binom(n,k,c) |- c1*(n-k+1) = c*k.
//checkentail 0 < k <= n & binom(n,k-1,c) & binom(n,k,d) |- c*(n-k+1) = d*k.
//proof by induction on n
//checkentail n = 1 & 0 < k <= n & binom(n,k-1,c) & binom(n,k,d) |- c*(n-k+1) = d*k.
//inductive case requires hard real number algebra
//checkentail n > 1 & forall(k1,c1,d1 : k1 <= 0 | k1 > n-1 | !(binom(n-1,k1-1,c1)) | !(binom(n-1,k1,d1)) | c1*(n-1-k1+1) = d1*k1) & 0 < k <= n & binom(n,k-1,c) & binom(n,k,d) |- c*(n-k+1) = d*k.

axiom n >= 0 |- binom(n,n,1).

axiom 0 < k <= n & binom(n,k-1,c1) & binom(n,k,c) |- c1*(n-k+1) = c*k.

//checkentail n >= 0 & binom(n,2,c) |- 2 * c = n * (n - 1).
checkentail n = 0 & binom(n,2,c) |- 2 * c = n * (n - 1).
checkentail n > 0 & forall(n1,c1 : n1 < 0 | n1 >= n | !(binom(n1,2,c1)) | 2*c1 = n1 * (n1 - 1)) & binom(n,2,c) |- 2 * c = n * (n - 1).

/*
int compute_binom(int n, int k)
	requires 0 <= k <= n
	ensures binom(n,k,res);
{
	if (n==k || k==0) 
		return 1;
	else {
		int c = compute_binom(n-1,k-1);
		int d = compute_binom(n-1,k);
		assert d' * k = c' * (n - k);
		assume d' * k = c' * (n - k);
		assert binom(n,k,c'+d');
		assume binom(n,k,c'+d');

		int r = idiv(n*c, k);
		//int r = n * c / k;
		assert r' = c'+d';
		assume r' = c'+d';

		return r;
	}
}

int idiv(int x, int y)
	requires y != 0
	ensures res * y = x;
*/
