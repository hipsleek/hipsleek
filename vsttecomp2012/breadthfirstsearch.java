data Graph {
	int[,] adj;				// adjacency matrix A[i,j] = 1 <==> j is a successor of i
	int num_vertices;		// number of vertices, index 0 to (num_vertices - 1)
}

/* We make three parallel recursive definitions: there is a path from s --> t of
        (i) no further restriction   (ii) length <= k        (iii) length exactly k
 <==>
  - Base case: 
        (i) s = t                    (ii) s = t & k >= 0     (iii) s = t & k = 0
  - Induction: there is a path from s to a predecesor of t of
        (i) no further restriction   (ii) length <= k - 1    (iii) length exactly k - 1
*/

relation has_path(int[,] A, int n, int s, int t) ==
	(s = t | exists(i : 0 <= i < n & has_path(A,n,s,i) & A[i,t] = 1)).
	
relation has_bounded_length_path(int[,] A, int n, int s, int t, int k) ==
	k >= 0 & (s = t | exists(i : 0 <= i < n & has_bounded_length_path(A,n,s,i,k-1) & A[i,t] = 1)).
	
relation all_has_bounded_length_path(int[,] A, int n, int s, int k, int[] V) ==
	forall(i : i < 0 | i >= n | 
				V[i] = 0 & !(has_bounded_length_path(A,n,s,i,k)) |
				V[i] != 0 & has_bounded_length_path(A,n,s,i,k)).
	
relation has_exact_length_path(int[,] A, int n, int s, int t, int k) ==
	(k = 0 & s = t | exists(i : 0 <= i < n & has_exact_length_path(A,n,s,i,k-1) & A[i,t] = 1)).
	
// Theorem: (non-trivial) if there is a path from s-->d then there is a path of length <= n
// Pf: For any path from s --> d, we can always construct a path with no duplicated vertices.
//     Since the graph has n vertices, such a path must be of length <= n.     (QED)
axiom has_path(A,n,s,t) ==> has_bounded_length_path(A,n,s,t,n).

// the shortest path from s --> t is of length d 
relation shortest_distance(int[,] A, int n, int s, int t, int d) ==
	has_exact_length_path(A, n, s, t, d) & !(has_bounded_length_path(A, n, s, t, d-1)).
	
relation all_has_shortest_distance(int[,] A, int n, int s, int d, int[] C) ==
	forall(i : i < 0 | i >= n | 
				C[i] = 0 & !(shortest_distance(A,n,s,i,d)) |
				C[i] != 0 & shortest_distance(A,n,s,i,d)).

int bfs(Graph G, int source, int target)
	requires G::Graph<A,n> & 0 <= source < n & 0 <= target < n
	ensures res < 0 & !(has_path(A,n,source,target)) 
			or res >= 0 & shortest_distance(A,n,source,target,res);
{
	int nv = G.num_vertices;
	int[] V = new int[nv];
	int[] C = new int[nv];
	
	init_false(V, nv); V[source] = 1; // V = {source}
	init_false(C, nv); C[source] = 1; // C = {source}
	
	return bfs_helper(G, source, target, 0, V, C);
}

int bfs_helper(Graph G, int source, int target, int d, ref int[] V, ref int[] C)
	requires G::Graph<A,n> & 0 <= source < n & 0 <= target < n & 
			dom(V,0,n-1) & dom(C,0,n-1) &
			all_has_bounded_length_path(A, n, source, d, V) &
			all_has_shortest_distance(A, n, source, d, C)
	ensures res < 0 & !(has_path(A,n,source,target))
			or res >= 0 & shortest_distance(A,n,source,target,res);
{
	int nv = G.num_vertices;
	if (is_empty(C, nv))
		return -1;
	else {
		int[] N = new int[nv];
		init_false(N, nv);
		int r = bfs_helper_helper(G, source, target, d, V, C, N, 0, 0);
		if (r >= 0)
			return r;
		else
			return bfs_helper(G, source, target, d + 1, V, N);
	}
}

/*
 Pre-condition:
 V[i] <==> there is a path source --> i of length at most
			.  d + 1 edges if 0 <= i < v
			.  d     edges if v <= i < n
 C[i] <==> the shortest path from source to i is of length d
 N[i] <==> the shortest path from source to i is of length d + 1
 */
int bfs_helper_helper(Graph G, int source, int target, int d, 
				ref int[] V, ref int[] C, ref int[] N,
				int v, int w)
	requires G::Graph<A,n> & 0 <= v <= n & 0 <= w <= n & 0 <= source < n & 0 <= target < n & 
			dom(V,0,n-1) & dom(C,0,n-1) & dom(N,0,n-1) & 
			all_has_bounded_length_path(A, n, source, d, V) &
			all_has_shortest_distance(A, n, source, d, C)
	ensures res < 0 & all_has_shortest_distance(A,n,source,d + 1,N')
			or res >= 0 & shortest_distance(A,n,source,target,res);
{
	if (v < G.num_vertices) {
		if (C[v] != 0) {
			if (v == target)
				return d;
			if (w < G.num_vertices) {
				if (G.adj[v,w] != 0 && V[w] == 0) {
					V[w] = 1;
					N[w] = 1;
				}
				// continue with next w
				return bfs_helper_helper(G, source, target, d, V, C, N, v, w + 1);
			}
			// w = n ==> we already exhaust all successor of v, continue with next v
		}
		// v is not in C, continue with next v
		return bfs_helper_helper(G, source, target, d, V, C, N, v + 1, 0);
	}
	return -1;
}

relation allzero(int[] A, int i, int j) ==
	forall(k : k < i | k > j | A[k] = 0).

void init_false(ref int[] A, int n)
	requires dom(A,0,n-1)
	ensures dom(A',0,n-1) & allzero(A',0,n-1);
{
	init_false(A, n, 0);
}

void init_false(ref int[] A, int n, int i)
	requires dom(A,0,n-1) & allzero(A,0,i-1) & 0 <= i
	ensures dom(A',0,n-1) & allzero(A',0,n-1);
{
	if (i < n) {
		A[i] = 0;
		init_false(A, n, i+1);
	}
}

bool is_empty(int[] C, int n)
	requires dom(C,0,n-1)
	ensures res & allzero(C,0,n-1) or !res & !(allzero(C,0,n-1));
{
	if (n > 0) {
		if (C[n-1] == 0)
			return false;
		return is_empty(C, n-1);
	}
	return true;
}
