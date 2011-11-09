data Graph {
	int[,] adj;			// adjacency matrix
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
	
relation has_exact_length_path(int[,] A, int n, int s, int t, int k) ==
	(k = 0 & s = t | exists(i : 0 <= i < n & has_exact_length_path(A,n,s,i,k-1) & A[i,t] = 1)).
	
// Theorem: (non-trivial) if there is a path from s-->d then there is a path of length <= n
// Pf: For any path from s --> d, we can always construct a path with no duplicated vertices.
//     Since the graph has n vertices, such a path must be of length <= n.     (QED)
axiom has_path(A,n,s,t) ==> has_bounded_length_path(A,n,s,t,n).

// the shortest path from s --> t is of length d 
relation shortest_distance(bool[,] A, int n, int s, int t, int d) ==
	has_exact_length_path(A, n, s, t, d) & !(has_bounded_length_path(A, n, s, t, d-1)).

int bfs(Graph G, int source, int target)
	requires G::Graph<A,n> & 0 <= source < n & 0 <= target < n
	ensures true;
{
/*	V <- {source};
	C <- {source};
	N <- {};
	d <- 0;
	while C is not empty do
		remove one vertex v from C;
		if v = dest then return d; endif
		for each w in succ(v) do
			if w is not in V then
				add w to V;
				add w to N;
			endif
		endfor
		if C is empty then
			C <- N;
			N <- {};
			d <- d+1;
		endif
	endwhile
	fail "no path" */
	
	bool[] V, N, C;
	assume domb(V,0,n-1) & domb(N,0,n-1) & domb(C,0,n-1);
	init_false(V, G.num_vertices);
	init_false(C, G.num_vertices);
	V[source] = true;
	C[source] = true;
	return bfs_helper(G, source, target, 0, V, C, N, 0, 0);
}

void init_false(bool[] A, int n) {
	init_false(A, n, 0);
}

void init_false(bool[] A, int n, int i) {
	if (i < n) {
		A[i] = false;
		init_false(A, n, i+1);
	}	
}
/*
Pre-condition:
 V[i] <==> there is a path source --> i of length at most
			.  d + 1 edges if 0 <= i < v
			.  d     edges if v <= i < n
 C[i] <==> the shortest path from source to i is of length d
 N[i] <==> the shortest path from source to i is of length d + 1
 Return shortest distance source-->target or -1
 */
bool bfs_helper(Graph G, int source, int target, int d, 
				ref bool[] V, bool[] C, ref bool[] N,
				int v, int w)
	requires G::Graph<A,n>
	ensures true;
{
	if (v < G.num_vertices) {
		if (C[v]) {
			if (v == target)
				return true;
			if (w < G.num_vertices) {
				bool bt = V[w];
				if (G.adj[v,w] && !bt) {
					// w is an unvisited successor of v
					V[w] = true;
					N[w] = true;
				}
				// continue with next w
				return bfs_helper(G, source, target, V, C, N, v, w + 1);
			}
			// w = n ==> we already exhaust all successor of v, continue with next v
		}
		// v is not in C, continue with next v
		return bfs_helper(G, source, target, V, C, N, v + 1, 0);
	}
	return -1;
}
