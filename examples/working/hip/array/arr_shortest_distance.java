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

relation non_negative(int[][] A, int n) == forall(i, j : i < 0 | i >= n | j < 0 | j >= n | A[i][j] >= 0).

relation has_path_length(int[][] A, int n, int i, int j, int l) ==
	(A[i][j] = l | exists(u : 0 <= u < n & A[i][u] > 0 & 
						has_path_length(A, n, u, i, l - A[i][u]))).

relation shortest_distance(int[][] A, int n, int i, int j, int d) ==
	has_path_length(A, n, i, j, d) & forall(l : !(has_path_length(A, n, i, j, l)) | d <= l).
	

/**
 Shortest distance algorithm using DP
 */ 
int shortest_distance(Graph G, int s)
{
	return 1;
}
