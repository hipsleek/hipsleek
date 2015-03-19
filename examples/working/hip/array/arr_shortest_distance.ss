/**
 * Djikstra shortest distance algorithm
 * TODO implement
 * 
 * @author Vu An Hoa
 */
 
data Graph {
	int[][] A; 	// adjacency matrix: A[i][j] = direct distance between node <i> and <j>
				// presumably all >= 0 and 0 if there is no edge between them
	int n;		// number of vertices, index from 0 to n-1
}

relation non_negative(int[][] A, int n) == 
	forall(i, j : i < 0 | i >= n | j < 0 | j >= n | A[i,j] >= 0).

// there is a path from s to e of length l
relation has_path_length(int[][] A, int n, int s, int e, int l) ==
	(A[i,j] = l | exists(u : 0 <= u < n & A[i,u] > 0 & 
						has_path_length(A, n, u, e, l - A[i,u]))).

// d is the shortest distance from s to e
relation shortest_distance(int[][] A, int n, int s, int e, int d) ==
	has_path_length(A, n, s, e, d) & forall(l : !(has_path_length(A, n, s, e, l)) | d <= l).

// d is the length of shortest path from s --> e
relation shortest_distance_k(int[][] A, int n, int k, int s, int e, int d) ==
	has_path_length(A, n, s, e, d) & forall(l : !(has_path_length(A, n, s, e, l)) | d <= l).	

/**
 Shortest distance algorithm using DP
 */ 
int shortest_distance(Graph G, int s, int e)
	requires G::Graph<A,n> & n >= 0 & 0 <= s < n & 0 <= e < n & non_negative(A, n)
	ensures shortest_distance(A, n, s, e, d);
{
	int k, v, u;
	
	// shortest[x] = shortest distance from x to e within k steps
	// -1 to indicate infinity i.e. no path consisting <= k intermediate
	// vertices joining x --> e
	int[] shortest = new int[n];
	
	// initialize
	k = 0;
	v = 0;
	while (v < n) {
		if (v == e)
			shortest[v] = 0;
		else
			shortest[v] = -1;
	}
	
	while (
	// recursive computation
	for(int k = 1; k <= n; k++) {
		for(int v = 0; v < n; v++) {
			for(int u = 0; u < n; u++) {
				if (shortest[u] != -1 || G.A[v,u] != 0) {
					int t = G.A[v,u] + shortest[u];
					if (shortest[v] == -1 || t < shortest[v])
						shortest[v] = t;
				}
			}
		}
	}
	
	return shortest[s];
	
}
