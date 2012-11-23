/* PRELIMINARY RELATIONS */ 
relation allzero(int[] A, int i, int j) == 
	forall(k : k < i | k > j | A[k] = 0).

// there is a path from s to t
relation has_path(int[,] A, int n, int s, int t) == 
	exists(d : 0 <= d & hemp(A,n,n,s,t,d)).

// well-ordering of integers
axiom has_path(A,n,s,t) ==> exists(d : msd(A,n,n,s,t,d)).

// there is a m-path from s to t of length exactly d
relation hemp(int[,] A, int n, int m, int s, int t, int d) ==
	0 <= m <= n & 0 <= s < n & 0 <= t < n & (d = 0 & s = t | 
	d > 0 & m > 0 & exists(i : 0 <= i < m & hemp(A,n,n,s,i,d-1) & A[i,t] != 0)).

// there is a m-path from s to t of length at most d
relation hbmp(int[,] A, int n, int m, int s, int t, int d) == 
	0 <= s < n & 0 <= t < n & (d = 0 & s = t | 
	d > 0 & 0 < m <= n & (hbmp(A,n,m,s,t,d-1) | hemp(A,n,m,s,t,d))). // exists(k : 0 <= k <= d & hemp(A,n,m,s,t,d))).

// the length of shortest m-path from s to t is d
relation msd(int[,] A, int n, int m, int s, int t, int d) == 
	0 <= s < n & 0 <= t < n & (d = 0 & s = t |
	d > 0 & 0 < m <= n & hemp(A,n,m,s,t,d) & !(hbmp(A,n,m,s,t,d-1))).

// Every vertices x such that x1 <= x < x2 belongs to S iff either there is a path of length <= d from s to x or there is a m-path of length d+1 from s to x
relation reach(int[,] A, int n, int m, int s, int[] S, int x1, int x2, int d) == x1 >= x2 | forall(x : x < x1 | x >= x2 | 
	S[x] = 0 & !(hbmp(A,n,n,s,x,d)) & !(hemp(A,n,m,s,x,d+1)) | 
	S[x] != 0 & hbmp(A,n,n,s,x,d) | 
	S[x] != 0 & hemp(A,n,m,s,x,d+1)).

// Every vertex x such that x1 <= x < x2 is in S if and only if the m-shortest-distance from s to x is d and that there is no path shorter than d from s to x
relation allsd(int[,] A, int n, int m, int s, int[] S, int x1, int x2, int d) == x1 >= x2 | forall(x : x < x1 | x >= x2 | 
	S[x] = 0 & !(msd(A,n,m,s,x,d)) | 
	S[x] = 0 & hbmp(A,n,n,s,x,d-1) | 
	S[x] != 0 & msd(A,n,m,s,x,d) & !(hbmp(A,n,n,s,x,d-1))).

/* NON-TRIVIAL THEOREMS */

// To prove precondition in case v is not in C in bfs_loop2
axiom !(msd(A,n,n,s,v,d)) & allsd(A,n,v,s,S,0,n,d+1) ==> allsd(A,n,v+1,s,S,0,n,d+1).

// expanded to the pair of theorems

//axiom !(msd(A,n,n,s,v,d)) & !(hbmp(A,n,n,s,t,d)) & msd(A,n,v,s,t,d+1) ==> msd(A,n,v+1,s,t,d+1).

//axiom !(msd(A,n,n,s,v,d)) & !(hbmp(A,n,n,s,t,d)) & msd(A,n,v+1,s,t,d+1) ==> msd(A,n,v+1,s,t,d+1).

// To prove post-condition of bfs_loop2; intuitively, 
// it says that there is no 0-path of non-zero length.
axiom reach(A,n,n,s,S,0,n,d) ==> reach(A,n,0,s,S,0,n,d+1).

// To prove pre-condition of recursive call in bfs_loop3 
// when the right-above if-condition is true. Intuitively,
// this axiom is due to the fact any m-path is an n-paths.
axiom !(hbmp(A,n,n,s,t,d)) ==> !(hbmp(A,n,m,s,t,d)).

/* ALGORITHM & SPECIFICATION */

int bfs(int[,] A, int n, int s, int t)
	requires 0 <= s < n & 0 <= t < n
	ensures res < 0 & !(has_path(A,n,s,t)) | 
			res >= 0 & msd(A,n,n,s,t,res);
{
	int[] V = new int[n]; init_false(V, n); V[s] = 1; // V = {s}
	int[] C = new int[n]; init_false(C, n); C[s] = 1; // C = {s}
	int d = 0;
	return bfs_loop1(A,n,s,t,d,V,C);
}

int bfs_loop1(int[,] A, int n, int s, int t, int d, int[] V, int[] C)
	requires 0 <= s < n & 0 <= t < n & d >= 0 &
			dom(V,0,n-1) & dom(C,0,n-1) &
			reach(A,n,0,s,V,0,n,d) &
			allsd(A,n,n,s,C,0,n,d) 
	ensures res < 0 & !(has_path(A,n,s,t)) | 
			res >= 0 & msd(A,n,n,s,t,res);
{
	if (is_empty(C,n)) {
		assume !(has_path(A,n,s,t));
		return -1;
	}
	else {
		int[] N = new int[n];
		init_false(N, n);
		int r = bfs_loop2(A,n,s,t,d,V,C,N,0);
		if (r >= 0)
			return r;
		else
			return bfs_loop1(A,n,s,t,d+1,V,N);
	}
}

int bfs_loop2(int[,] A, int n, int s, int t, int d, ref int[] V, int[] C, ref int[] N, int v)
	requires 0 <= s < n & 0 <= t < n & d >= 0 & 0 <= v <= n &
		dom(V,0,n-1) & dom(C,0,n-1) & dom(N,0,n-1) & 
		reach(A,n,v,s,V,0,n,d) &
		allsd(A,n,n,s,C,0,n,d) &
		allsd(A,n,v,s,N,0,n,d+1)
	ensures res < 0 & 
		reach(A,n,0,s,V',0,n,d+1) &
		allsd(A,n,n,s,N',0,n,d+1) &
		dom(V',0,n-1) & dom(N',0,n-1) |
		res >= 0 & msd(A,n,n,s,t,res);
{
	if (v < n) {
		if (C[v] != 0) {
			if (v == t)
				return d;
			bfs_loop3(A,n,s,t,d,V,N,v,0);
		}
		return bfs_loop2(A,n,s,t,d,V,C,N,v+1);
	}
	return -1;
}

void bfs_loop3(int[,] A, int n, int s, int t, int d, ref int[] V, ref int[] N, int v, int w)
	requires 0 <= s < n & 0 <= t < n & 
		d >= 0 & 0 <= v < n & 0 <= w <= n & 
		dom(V,0,n-1) & dom(N,0,n-1) & 
		msd(A,n,n,s,v,d) &
		reach(A,n,v+1,s,V,0,w,d) &
		reach(A,n,v,s,V,w,n,d) &
		allsd(A,n,v+1,s,N,0,w,d+1) &
		allsd(A,n,v,s,N,w,n,d+1)
	ensures reach(A,n,v+1,s,V',0,n,d) &
		allsd(A,n,v+1,s,N',0,n,d+1) &
		dom(V',0,n-1) & dom(N',0,n-1);
{
	if (w < n) {
		if (A[v,w] != 0 && V[w] == 0) {
			V[w] = 1;
			N[w] = 1;
		}
		bfs_loop3(A,n,s,t,d,V,N,v,w+1);
	}
}

// Initialize all of A[0..n-1] to 0
void init_false(ref int[] A, int n)
	requires dom(A,0,n-1) & n >= 0
	ensures dom(A',0,n-1) & allzero(A',0,n-1);
{
	//for(int i = 0; i < n; i++) A[i] = 0;
	init_false(A, n, 0);
}

// Helper function expanding for loop 
void init_false(ref int[] A, int n, int i)
	requires dom(A,0,n-1) & allzero(A,0,i-1) & 0 <= i <= n
	ensures dom(A',0,n-1) & allzero(A',0,n-1);
{
	if (i < n) {
		A[i] = 0;
		init_false(A, n, i+1);
	}
}

// Check if the set C[0..n-1] is empty
bool is_empty(int[] C, int n)
	requires dom(C,0,n-1) & n >= 0
	ensures res & allzero(C,0,n-1) or !res & !(allzero(C,0,n-1));
{
	if (n > 0) {
		if (C[n-1] != 0)
			return false;
		return is_empty(C, n-1);
	}
	return true;
}
