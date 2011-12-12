/**
 VSTTE 2012 Competition
 Problem 5 : Breadth First Search
 */

relation allzero(int[] A, int i, int j) == 
	forall(k : k < i | k > j | A[k] = 0).
	
relation has_path(int[,] A, int n, int s, int t) == (s = t | exists(i : 0 <= i < n & has_path(A,n,s,i) & A[i,t] != 0)).

// there exists a v-path from s to t of length d
relation has_exact_length_v_path(int[,] A, int n, int v, int s, int t, int d) == (d = 0 & s = t | d > 0 & exists(i : 0 <= i < v & has_exact_length_v_path(A,n,n,s,i,d-1) & A[i,t] != 0)).

// there exists a v-path from s to t of length at most d
relation has_bounded_length_v_path(int[,] A, int n, int v, int s, int t, int d) == exists(k : 0 <= k <= d & has_exact_length_v_path(A,n,v,s,t,d)).

// the length of shortest v-path from s to t is d
relation v_shortest_distance(int[,] A, int n, int v, int s, int t, int d) == has_exact_length_v_path(A,n,v,s,t,d) & !(has_bounded_length_v_path(A,n,v,s,t,d-1)).

// shortest distance is the same as n-shortest-distance
relation shortest_distance(int[,] A, int n, int s, int t, int d) == v_shortest_distance(A,n,n,s,t,d).

// Every vertices x such that x1 <= x < x2 belongs to S iff either there is a path of length <= d from s to x or there is a v-path of length d+1 from s to x
relation reachable(int[,] A, int n, int v, int s, int[] S, int x1, int x2, int d) == forall(x : x < x1 | x >= x2 | S[x] = 0 & !(has_bounded_length_v_path(A,n,n,s,x,d)) & !(has_exact_length_v_path(A,n,v,s,x,d+1)) | S[x] != 0 & (has_bounded_length_v_path(A,n,n,s,x,d) | has_exact_length_v_path(A,n,v,s,x,d+1))).

// Every vertex x such that x1 <= x < x2 is in S if and only if the v-shortest-distance from s to x is d
relation allvsd(int[,] A, int n, int v, int s, int[] S, int x1, int x2, int d) == forall(x : x < x1 | x >= x2 | S[x] = 0 & !(v_shortest_distance(A,n,v,s,x,d)) | S[x] != 0 & v_shortest_distance(A,n,v,s,x,d)).

// THEOREMS REQUIRED FOR PRE-CONDITION I.E. LOOP INVARIANTS

// AXIOM 1 - bfs_loop3
axiom has_bounded_length_v_path(A,n,v,s,x,d) & v_shortest_distance(A,n,v+1,s,x,d) ==> v_shortest_distance(A,n,v,s,x,d).

// AXIOM 2 - precondition to recursive call bfs_loop2 in bfs_loop2
axiom !(shortest_distance(A,n,s,v,d)) & has_exact_length_v_path(A,n,v+1,s,x,d+1) & !(has_bounded_length_v_path(A,n,n,s,x,d)) ==> has_exact_length_v_path(A,n,v,s,x,d+1).

// AXIOM 3a - precondition to call recursive bfs_loop2 in bfs_loop2
axiom !(shortest_distance(A,n,s,v,d)) & v_shortest_distance(A,n,v,s,x,d+1) ==> v_shortest_distance(A,n,v+1,s,x,d+1).

// AXIOM 3b - precondition to call recursive bfs_loop2 in bfs_loop2
axiom !(shortest_distance(A,n,s,v,d)) & v_shortest_distance(A,n,v+1,s,x,d+1) ==> v_shortest_distance(A,n,v,s,x,d+1).

// to prove precondition to recursive call to bfs_loop1 in bfs_loop1.
axiom reachable(A,n,n,s,V,0,n,d) ==> reachable(A,n,0,s,V,0,n,d+1).

int bfs(int[,] A, int n, int s, int t)
	requires 0 <= s < n & 0 <= t < n
	ensures res < 0 & !(has_path(A,n,s,t)) | 
			res >= 0 & shortest_distance(A,n,s,t,res);
{
	int[] V = new int[n];
	init_false(V, n);
	V[s] = 1; // V = {s}

	int[] C = new int[n];
	init_false(C, n);
	C[s] = 1; // C = {s}
	
	int d = 0;
	
	//assume reachable(A,n,0,s,V',0,n,0);
	//assume allvsd(A,n,n,s,C',0,n,0);
	
	return bfs_loop1(A,n,s,t,d,V,C);
}

// Find shortest distance from s to t given:
//   .  the set V consisting of vertices reachable within d arcs; and
//   .  the set C of vertices with shortest distance d from s
int bfs_loop1(int[,] A, int n, int s, int t, int d, int[] V, int[] C)
	requires 0 <= s < n & 0 <= t < n & d >= 0 &
			dom(V,0,n-1) & dom(C,0,n-1) &
			reachable(A,n,0,s,V,0,n,d) &
			allvsd(A,n,n,s,C,0,n,d)
	ensures res < 0 & !(has_path(A,n,s,t)) | 
			res >= 0 & shortest_distance(A,n,s,t,res);
{
	if (is_empty(C,n)) {
		// Non-trivial Theorem: (Completeness)
		// If there is no vertex with shortest distance d then 
		// there is no vertex with shortest distance > d. Proof: Suppose that there
		// is a vertex v with a shortest path {src = x_0, x_1, ..., x_k = v} for k > d. 
		// Then x_d must be of shortest distance d; otherwise, we can replace part of 
		// the original path, namely {x_0,x_1,...,x_d}, and obtain a shorter path for 
		// x_k. Contradiction!
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
		reachable(A,n,v,s,V,0,n,d) &
		allvsd(A,n,n,s,C,0,n,d) &
		allvsd(A,n,v,s,N,0,n,d+1)
	ensures res < 0 & 
		reachable(A,n,n,s,V',0,n,d) &
		allvsd(A,n,n,s,N',0,n,d+1) &
		dom(V',0,n-1) & dom(N',0,n-1) | 
		res >= 0 & shortest_distance(A,n,s,t,res);
{
	if (v < n) {
		if (C[v] != 0) {
			if (v == t)
				return d;
			bfs_loop3(A, n, s, t, d, V, N, v, 0);
		}
		return bfs_loop2(A, n, s, t, d, V, C, N, v + 1);
	}
	return -1;
}

void bfs_loop3(int[,] A, int n, int s, int t, int d, ref int[] V, ref int[] N, int v, int w)
	requires 0 <= s < n & 0 <= t < n & 
		d >= 0 & 0 <= v < n & 0 <= w <= n & 
		dom(V,0,n-1) & dom(N,0,n-1) & 
		v_shortest_distance(A,n,n,s,v,d) &
		reachable(A,n,v+1,s,V,0,w,d) &
		reachable(A,n,v,s,V,w,n,d) &
		allvsd(A,n,v+1,s,N,0,w,d+1) &
		allvsd(A,n,v,s,N,w,n,d+1)
	ensures reachable(A,n,v+1,s,V',0,n,d) &
		allvsd(A,n,v+1,s,N',0,n,d+1) &
		dom(V',0,n-1) & dom(N',0,n-1);
{
	if (w < n) {
		assume A[v,w] != 0 & V[w] = 0;
		if (A[v,w] != 0 && V[w] == 0) {
			assert has_exact_length_v_path(A,n,v+1,s,w,d+1);
			assume has_exact_length_v_path(A,n,v+1,s,w,d+1);
			assert !(has_bounded_length_v_path(A,n,n,s,w,d));
			assume !(has_bounded_length_v_path(A,n,v+1,s,w,d));
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
