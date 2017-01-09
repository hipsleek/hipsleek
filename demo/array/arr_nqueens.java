/**
 * Problem 4 in VSComp 2010: N-Queens
 * @author Vu An Hoa
 * @date 24/06/2011
 */

/** RELATIONS **/

//relation dom(int[] a, int l, int h) == true.

relation IdenticalRange(int[] a, int[] b, int i, int j) ==
	forall(k : (k < i | k > j | a[k] = b[k])).

//Queens i & j are not attacking each other
relation AreNotAttackingQueens(int[] b, int i, int j) == 
	(i = j | b[j] != b[i] & b[j] - b[i] != j - i & b[j] - b[i] != i - j).

// Queen i is safe with respect to other queens
relation IsSafeQueen(int[] b, int i) ==
	forall(j : (j < 1 | j >= i | AreNotAttackingQueens(b,i,j))).

// Board b[m..n] is consistent if and only if every queen [m..n] is safe.
relation IsConsistent(int[] b, int m, int n) ==
	//the nested forall formulation does not work!
	//forall(i : (i < 1 | i > n | IsSafeQueen(b,i))).
	forall(i, j: (i < m | i > n | j < m | j >= i |
		b[j] != b[i] & b[j] - b[i] != j - i & b[j] - b[i] != i - j)).

// There is no solution with prefix b[1..i] and b[i+1] in {1..k}, k <= n.
relation NoSolutionPrefix(int[] b, int n, int i, int k) ==
	// base case: i >= n & b[1..n] is inconsistent
	k <= n & (i >= n & !(IsConsistent(b,1,n))
	// induction: for any choice of b[i+1] in {1..n}, there is 
	// no solution with prefix b[1..i+1]
	| forall(j: (j < 1 | j > k | b[i+1] != j | NoSolutionPrefix(b,n,i+1,n)))).

// Axiom saying that if b[1..i] is already inconsistent, it cannot be
// extend to a solution of the n-queens problem (if i <= n of course).
// This axiom requires a proof by induction.
axiom !(IsConsistent(b,1,i)) & i <= n ==> NoSolutionPrefix(b,n,i,n).

relation Bounded(int[] a, int i, int j, int l, int h) ==
	(forall(k : (k < i | k > j | l <= a[k] & a[k] <= h))).

/** FUNCTIONS **/

// Solve n-queens
// @return 	false if there is no solution
// 			true if there is a solution; in such case, the resulting 
//					array b gives a valid solution
bool nQueens(ref int[] b, int n)
	requires dom(b,1,n) & 1 <= n
	ensures (res & IsConsistent(b',1,n) & Bounded(b',1,n,1,n) | !res & NoSolutionPrefix(b',n,0,n));
{
	return nQueensHelper(b, n, 1);
}

// Back-tracking search algorithm
// @param i The current stage, b[1..i-1] is a partial solution
bool nQueensHelper(ref int[] b, int n, int i)
	requires dom(b,1,n) & 1 <= i <= n+1 & IsConsistent(b,1,i-1) & Bounded(b',1,i-1,1,n) 
	ensures dom(b',1,n) & 
			(res & IsConsistent(b',1,n) & Bounded(b',1,n,1,n) | !res & NoSolutionPrefix(b',n,i-1,n)) & 
			IdenticalRange(b',b,1,i-1);
{
	if (i == n + 1) // nothing more to search!
		return true;
	else {
//		for(b[i] = 1; b[i] <= n; b[i]++) {
//			if (IsSafe(b,n,i))
//				if (nQueensHelper(b,n,i+1))
//					return true;
//		}
		
		return nQueensHelperHelper(b, n, i, 1);
	}
}

// Expansion of the for-loop in nQueensHelper
// @param j Indicate that the choice b[i] in {1,...,j-1} is not valid; try
// the rest of the values from {j,...,n}
bool nQueensHelperHelper(ref int[] b, int n, int i, int j)
	requires dom(b,1,n) & 1 <= i <= n & 1 <= j <= n + 1 
				& IsConsistent(b,1,i-1) & NoSolutionPrefix(b,n,i-1,j-1)
				& Bounded(b',1,i-1,1,n) 
	ensures dom(b',1,n) & 
			(res & IsConsistent(b',1,n) & Bounded(b',1,n,1,n) | !res & NoSolutionPrefix(b',n,i-1,n)) & 
			IdenticalRange(b',b,1,i-1);
{
	if (j <= n) {
		b[i] = j; // try putting a queen at (i,j)
		if (IsSafe(b,n,i)) {
			// safe ==> try the next queen
			if (nQueensHelper(b,n,i+1)) 
				return true; 	// find a solution
			else
				return nQueensHelperHelper(b, n, i, j + 1);	// cannot find solution, try the next option
		}
	}
	return false;	// call when j > n i.e. j = n+1 or when (i,j) is not a safe position
}

// Check if b[1..i] is consistent.
// @return true if b[1..i] is consistent
//		false if it is not; i.e. there is no solution with this prefix.
bool IsSafe(int[] b, int n, int i)
	requires dom(b,1,n) & 1 <= i <= n & IsConsistent(b,1,i-1)
	ensures  (res & IsConsistent(b,1,i) | !res & NoSolutionPrefix(b,n,i,n));
{
//	for(int j = i-1; j > 0; j--) {
//		int h = b[i] - b[j];
//		if (h == 0 || h == i - j || h == j - i)
//			return false;
//	}
//	return true;
	
	return IsSafeHelper(b,n,i,i-1);
}

// Expand the for-loop in IsSafe
bool IsSafeHelper(int[] b, int n, int i, int j)
	requires dom(b,1,n) & 1 <= i <= n & 0 <= j < i
				& IsConsistent(b,1,i-1) & IsConsistent(b,j+1,i)
	ensures (res & IsConsistent(b,1,i) | !res & NoSolutionPrefix(b,n,i,n));
{
	if (j == 0)
		return true;
	else {
		int h = b[i] - b[j];
		if (h == 0 || h == i - j || h == j - i)
			return false;
		return IsSafeHelper(b,n,i,j-1);
	}
}
