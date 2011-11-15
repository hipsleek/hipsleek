/**
 VSTTE 2012 Competition
 Problem 5 : Breadth First Search
 
 Let us fix the terminology 
 */

relation allzero(int[] A, int i, int j) == forall(k : k < i | k > j | A[k] = 0).

/* We make three parallel recursive definitions: there is a path from s --> t of
        (i) no further restriction   (ii) length <= k        (iii) length exactly k
 <==>
  - Base case: 
        (i) s = t                    (ii) s = t & k >= 0     (iii) s = t & k = 0
  - Induction: there is a path from s to a predecesor of t of
        (i) no further restriction   (ii) length <= k - 1    (iii) length exactly k - 1
*/
relation has_path(int[,] A, int n, int s, int t) ==
	(s = t 
	| exists(i : 0 <= i < n & has_path(A,n,s,i) & A[i,t] != 0)).

relation has_bounded_length_path(int[,] A, int n, int s, int t, int k) ==
	(k >= 0 & s = t | 
	k > 0 & exists(i : 0 <= i < n & has_bounded_length_path(A,n,s,i,k-1) & A[i,t] != 0)).
	
relation has_exact_length_path(int[,] A, int n, int s, int t, int k) ==
	(k = 0 & s = t
	| k > 0 & exists(i : 0 <= i < n & has_exact_length_path(A,n,s,i,k-1) & A[i,t] != 0)).

// d is the shortest distance between s and t
relation shortest_distance(int[,] A, int n, int s, int t, int d) ==
	has_exact_length_path(A, n, s, t, d) & !(has_bounded_length_path(A, n, s, t, d-1)).

// Existence of paths with restriction on the last intermediate vertex

relation has_bounded_length_path_via(int[,] A, int n, int s, int t, int k, int v) ==
	k > 0 & (has_bounded_length_path(A,n,s,t,k-1) 
			| exists(i : 0 <= i < v & has_exact_length_path(A,n,s,i,k-1) & A[i,t] != 0)).

relation has_exact_length_path_via(int[,] A, int n, int s, int t, int k, int v) ==
	(k = 0 & s = t 
	| exists(i : 0 <= i < v & has_exact_length_path(A,n,s,i,k-1) & A[i,t] != 0)).
		
relation shortest_distance_via(int[,] A, int n, int s, int t, int d, int v) ==
	has_exact_length_path_via(A, n, s, t, d, v) & 
	!(has_bounded_length_path_via(A, n, s, t, d-1, v)).

// Generalization of individual relations to a set of vertices

// All v in V is of distance <= d from s.
relation all_has_bounded_length_path(int[,] A, int n, int s, int d, int[] V) ==
	forall(i : i < 0 | i >= n | 
			V[i] = 0 & !(has_bounded_length_path(A,n,s,i,d)) |
			V[i] != 0 & has_bounded_length_path(A,n,s,i,d)).
			
relation all_has_bounded_length_path_via(int[,] A, int n, int s, int d, int[] V, int v) ==
	forall(i : i < 0 | i >= n | 
			V[i] = 0 & !(has_bounded_length_path_via(A,n,s,i,d,v)) |
			V[i] != 0 & has_bounded_length_path_via(A,n,s,i,d,v)).
			
relation some_has_bounded_length_path_via(int[,] A, int n, int s, int d, int[] V, int v, int w1, int w2) ==
	forall(i : i < w1 |i >= w2 | 
			V[i] = 0 & !(has_bounded_length_path_via(A,n,s,i,d,v)) |
			V[i] != 0 & has_bounded_length_path_via(A,n,s,i,d,v)).

relation all_has_shortest_distance(int[,] A, int n, int s, int d, int[] C) ==
	forall(i : i < 0 | i >= n | 
			C[i] = 0 & !(shortest_distance(A,n,s,i,d)) |
			C[i] != 0 & shortest_distance(A,n,s,i,d)).

relation all_has_shortest_distance_via(int[,] A, int n, int s, int k, int[] N, int v) ==
	forall(i : i < 0 | i >= n | 
			N[i] = 0 & !(shortest_distance_via(A,n,s,i,k,v)) |
			N[i] != 0 & shortest_distance_via(A,n,s,i,k,v)).

relation some_has_shortest_distance_via(int[,] A, int n, int s, int d, int[] N, int v, int w1, int w2) ==
	forall(i : i < w1 | i >= w2 | 
				N[i] = 0 & !(shortest_distance_via(A,n,s,i,d,v)) |
				N[i] != 0 & shortest_distance_via(A,n,s,i,d,v)).

// Theorem: (non-trivial) if there is a path from s-->d then there is a path of length <= n
// Pf: For any path from s --> d, we can always construct a path with no duplicated vertices.
//     Since the graph has n vertices, such a path must be of length <= n.     (QED)
// axiom has_path(A,n,s,t) ==> has_bounded_length_path(A,n,s,t,n).

// THEOREMS REQUIRED FOR PRE-CONDITION I.E. LOOP INVARIANTS

// AXIOM 1
axiom !(shortest_distance(A,n,s,v,d)) & all_has_bounded_length_path_via(A,n,source,d+1,V,v) ==> all_has_bounded_length_path_via(A,n,source,d+1,V,v+1).

// AXIOM 2
axiom !(shortest_distance(A,n,s,v,d)) & all_has_shortest_distance_via(A,n,source,d+1,N,v) ==> all_has_shortest_distance_via(A,n,source,d+1,N,v+1).

// AXIOM 3
axiom shortest_distance(A,n,s,v,d) & A[v,w] != 0 & !(has_bounded_length_path_via(A,n,s,w,d,v)) ==> shortest_distance_via(A,n,s,w,d+1,v+1).

// AXIOM 4
axiom shortest_distance_via(A,n,s,w,d,v) ==> has_bounded_length_path_via(A,n,s,w,d,v+1).

// THEOREMS REQUIRED FOR POST-CONDITION

// AXIOM 5
axiom all_has_bounded_length_path_via(A,n,source,d,V,n) ==> all_has_bounded_length_path(A,n,source,d,V).
	
// AXIOM 6
axiom all_has_shortest_distance_via(A,n,source,d+1,N,n) ==> all_has_shortest_distance(A,n,source,d+1,N).

// PROGRAM

int bfs(int[,] A, int n, int source, int target)
	requires 0 <= source < n & 0 <= target < n
	ensures res < 0 & !(has_path(A,n,source,target)) | 
			res >= 0 & shortest_distance(A,n,source,target,res);
{
	int[] V = new int[n];
	init_false(V, n);
	V[source] = 1; // V = {source}

	int[] C = new int[n];
	init_false(C, n);
	C[source] = 1; // C = {source}
	
	int d = 0;
	
	return bfs_loop1(A,n,source,target,d,V,C);
}

// Find shortest distance from source to target given:
//   .  the set V consisting of vertices reachable within d arcs; and
//   .  the set C of vertices with shortest distance d from source
int bfs_loop1(int[,] A, int n, int source, int target, int d, int[] V, int[] C)
	requires 0 <= source < n & 0 <= target < n & d >= 0 &
			dom(V,0,n-1) & dom(C,0,n-1) &
			all_has_bounded_length_path(A,n,source,d,V) &
			all_has_shortest_distance(A,n,source,d,C)
	ensures res < 0 & !(has_path(A,n,source,target)) | 
			res >= 0 & shortest_distance(A,n,source,target,res);
{
	if (is_empty(C,n)) {
		// Non-trivial Theorem: (Completeness)
		// If there is no vertex with shortest distance d then 
		// there is no vertex with shortest distance > d. Proof: Suppose that there
		// is a vertex v with a shortest path {src = x_0, x_1, ..., x_k = v} for k > d. 
		// Then x_d must be of shortest distance d; otherwise, we can replace part of 
		// the original path, namely {x_0,x_1,...,x_d}, and obtain a shorter path for 
		// x_k. Contradiction!
		assume !(has_path(A,n,source,target));
		return -1;
	}
	else {
		int[] N = new int[n];
		init_false(N, n);
		assume all_has_bounded_length_path_via(A,n,source,d,V,0);
		int r = bfs_loop2(A,n,source,target,d,V,C,N,0);
		if (r >= 0)
			return r;
		else
			return bfs_loop1(A,n,source,target,d+1,V,N);
	}
}

// Construct the set N of vertices whose shortest distance from source is d + 1 given
//   .  the set V of vertex such that all vertex v in V is either reachable within d ars 
//      or in exactly d+1 arcs with the final intermediate vertex is in {0,1,...,v-1}
//   .  the set C of vertices with shortest distance d from source
//   .  partially constructed N: x in N <==> x has shortest distance d+1 if the last
//      intermediate vertex is in {0,1,...,v-1}
int bfs_loop2(int[,] A, int n, int source, int target, int d, 
						ref int[] V, int[] C, ref int[] N, int v)
	requires 0 <= source < n & 0 <= target < n & d >= 0 & 0 <= v <= n &
			dom(V,0,n-1) & dom(C,0,n-1) & dom(N,0,n-1) &
			all_has_shortest_distance(A,n,source,d,C) &
			all_has_bounded_length_path_via(A,n,source,d+1,V,v) &
			all_has_shortest_distance_via(A,n,source,d+1,N,v)
	ensures res < 0 & all_has_bounded_length_path(A,n,source,d+1,V') & 
			all_has_shortest_distance(A,n,source,d+1,N') & 
			dom(V',0,n-1) & dom(N',0,n-1) | 
			res >= 0 & shortest_distance(A,n,source,target,res);
{
	if (v < n) {
		if (C[v] != 0) {
			if (v == target)
				return d;
			bfs_loop3(A, n, source, target, d, V, C, N, v, 0);
		}
		return bfs_loop2(A, n, source, target, d, V, C, N, v + 1);
	}
	return -1;
}

// Construct the set N of vertices whose shortest distance from source is d+1 if the last
// intermediate vertex is in {0,1,...,v-1} given
//   .  the set V of vertex such that all vertex v in V is reachable within d + 1
//      arcs and vertex not in V has no path of length <= d; and
//   .  the set C of vertices with shortest distance d from source
//   .  partially constructed N: for any 0 <= x < w: x in N <==> x has shortest distance 
//      d+1 with the last intermediate vertex is in {0,1,...,v-1}
void bfs_loop3(int[,] A, int n, int source, int target, int d, 
							ref int[] V, int[] C, ref int[] N, int v, int w)
	requires 0 <= source < n & 0 <= target < n & d >= 0 & 0 <= v < n & 0 <= w <= n & 
			dom(V,0,n-1) & dom(C,0,n-1) & dom(N,0,n-1) & 
			some_has_bounded_length_path_via(A,n,source,d+1,V,v+1,0,w) &
			some_has_bounded_length_path_via(A,n,source,d+1,V,v,w,n) &
			all_has_shortest_distance(A,n,source,d,C) &
			some_has_shortest_distance_via(A,n,source,d+1,N,v+1,0,w) &
			some_has_shortest_distance_via(A,n,source,d+1,N,v,w,n) &
			shortest_distance(A,n,source,v,d)
	ensures all_has_bounded_length_path_via(A,n,source,d+1,V',v+1) &
			all_has_shortest_distance_via(A,n,source,d+1,N',v+1) &
			dom(V',0,n-1) & dom(N',0,n-1);
{
	if (w < n) {
		if (A[v,w] != 0 && V[w] == 0) {
			V[w] = 1;
			N[w] = 1;
		}
		bfs_loop3(A, n, source, target, d, V, C, N, v, w + 1);
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
