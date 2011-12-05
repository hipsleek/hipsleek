/**
 * Djikstra shortest distance algorithm
 * TODO implement
 * 
 * @author Vu An Hoa
 */
 
// A[0..n-1,0..n-1] is >=0 with 0 indicating no path
relation nonneg(int[,] A, int n) == 
	forall(i, j : i < 0 | i >= n | j < 0 | j >= n | A[i,j] >= 0).

// there is a path with <= k edges from i to j of length l
relation kpath(int[,] A, int n, int i, int j, int k) ==
	k >= 0 & (i = j | exists(u : 0 <= u < n & A[i,u] > 0 & kpath(A, n, u, j, k - 1))).

// there is a path with <= k edges from i to j of length l
relation kpathl(int[,] A, int n, int i, int j, int k, int l) ==
	kpathlc(A, n, i, j, k, l, n - 1).	
	//k >= 0 & (i = j & l = 0 | exists(u : 0 <= u < n & A[i,u] > 0 & kpathl(A, n, u, j, k - 1, l - A[i,u]))).
	
// there is a path with <= k edges from i to j of length l with the first vertex reach from
// i is <= umax
relation kpathlc(int[,] A, int n, int i, int j, int k, int l, int umax) ==
	k >= 0 & umax < n & (i = j & l = 0 | exists(u : 0 <= u <= umax & A[i,u] > 0 & kpathlc(A, n, u, j, k - 1, l - A[i,u], n - 1))).
	
// there is a path with <= k edges from i to j of length l
relation nokpath(int[,] A, int n, int i, int j, int k, int umax) ==
	i != j & forall(u : u < 0 | u > umax | !(kpath(A, n, u, j, k - 1))).
	
// d is the length of shortest path within k edges from i --> j
relation ksdist(int[,] A, int n, int i, int j, int k, int d) ==
	ksdistvia(A, n, i, j, k, d, n - 1).
	//kpathl(A, n, i, j, k, d) & forall(l : !(kpathl(A, n, i, j, k, l)) | d <= l).
	
relation ksdistvia(int[,] A, int n, int i, int j, int k, int d, int vmax) ==
	kpathlc(A, n, i, j, k, d, vmax) & forall(l : !(kpathlc(A, n, i, j, k, l, vmax)) | d <= l).

axiom nonneg(A,n) & i = j & k >= 0 ==> ksdist(A,n,i,j,k,0).

axiom nokpath(A,n,i,j,k,n-1) ==> !(kpath(A,n,i,j,k)).

axiom ksdist(A,n,i,j,k,d) & nonneg(A,n) ==> d >= 0.

//axiom true ==> nokpath(A,n,i,j,k,-1).

axiom A[i,v] = 0 & nokpath(A,n,i,j,k,v-1) ==> nokpath(A,n,i,j,k,v).

axiom A[i,v] = 0 & ksdistvia(A,n,i,j,k,d,v-1) ==> ksdistvia(A,n,i,j,k,d,v).

/*
// Compute shortest distance s --> e via <= k edges; 
// -1 if there is no path from s --> e within k edges
int sdk(int[,] A, int n, int s, int e, int k)
	requires nonneg(A,n) & 0 <= s < n & 0 <= e < n & n >= 0 & k >= 0
	ensures (res >= 0 & ksdist(A,n,s,e,k,res) | res < 0 & !(kpath(A,n,s,e,k)));
{
	if (s == e)
		return 0;
		
	if (k == 0) // & s != e
		return -1;
	
	return sdkhelper(A, n, s, e, k, 0, -1);
}

int sdkhelper(int[,] A, int n, int s, int e, int k, int v, int m) 
	requires nonneg(A, n) & 0 <= s < n & 0 <= e < n & n >= 0 & 0 <= v <= n & k > 0 & s != e
	case {
		m < 0 -> requires nokpath(A,n,s,e,k,v-1)
				ensures (res >= 0 & ksdist(A,n,s,e,k,res) | res < 0 & !(kpath(A,n,s,e,k)));
		m >= 0 -> requires ksdistvia(A,n,s,e,k,m,v - 1)
				ensures res >= 0 & ksdist(A,n,s,e,k,res);
	}
{
	if (v < n) {
		if (A[s,v] != 0) {
			int r = sdk(A, n, v, e, k - 1);
			if (r >= 0) {
				r = A[s,v] + r;
				if (m < 0 || m > r) {
					m = r;
				}
			}
		}
		assume m' < 0 | m' >= 0 & ksdistvia(A,n,s,e,k,m',v);
		return sdkhelper(A, n, s, e, k, v + 1, m);
	}

	return m;
}
*/

// S[0..vmax] contains k-shortest-distance from v-->e
// S[v] < 0 when there is no k-path v-->e
relation allksdist(int[,] A, int n, int e, int k, int[] S, int vmax) ==
	forall(v : v < 0 | v > vmax | S[v] < 0 & !(kpath(A,n,v,e,k)) | ksdist(A,n,v,e,k,S[v])).

void dpsdk(int[,] A, int n, int e, int k, ref int[] S, int v)
	requires nonneg(A,n) & dom(S,0,n-1) & allksdist(A,n,e,k,S,v-1) & 
			0 <= e < n & n >= 0 & k >= 0  & 0 <= v <= n
	ensures allksdist(A,n,e,k,S',n-1) & dom(S',0,n-1);
{
	if (v < n) {
		if (v == e)
			S[v] = 0;
		else if (k == 0)
			S[v] = -1;
		else {
			int[] T = new int[n];
			dpsdk(A,n,e,k-1,T,0);
			S[v] = dpsdkfindmin(A,n,e,k,T,v,0,-1);
		}
		dpsdk(A, n, e, k, S, v + 1);
	}
}

int dpsdkfindmin(int[,] A, int n, int e, int k, int[] T, int v, int u, int m)
	requires nonneg(A,n) & dom(T,0,n-1) & allksdist(A,n,e,k-1,T,n-1) & 
			0 <= e < n & n >= 0 & k > 0  & 0 <= v <= n & 0 <= u <= n & v!=e
	case {
		m < 0 -> requires nokpath(A,n,v,e,k,u-1)
				ensures (res >= 0 & ksdist(A,n,v,e,k,res) | res < 0 & !(kpath(A,n,v,e,k)));
		m >= 0 -> requires ksdistvia(A, n, v, e, k, m, u - 1)
			ensures ksdist(A, n, v, e, k, res);
	}
{
	if (u < n) {
		if (A[v,u] > 0 && T[u] >= 0) {
			if (m < 0 || m >= 0 && m < A[v,u] + T[u])
				m = A[v,u] + T[u];
		}
		assume m' < 0 | m' >= 0 & ksdistvia(A,n,v,e,k,m',u);
		return dpsdkfindmin(A, n, e, k, T, v, u + 1, m);
	}
	return m;
}
