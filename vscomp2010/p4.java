/**
 Problem 4 in VSComp 2010: N-Queens
 @author Vu An Hoa
 @date 24/06/2011
 **/

/** RELATIONS **/

relation dom(int[] a, int l, int h) == true.

relation IdenticalRange(int[] a, int[] b, int i, int j) ==
	forall(k : (k < i | k > j | a[k] = b[k])).

//Queens i & j are not attacking each other
relation AreNotAttackingQueens(int[] b, int i, int j) == 
	(i = j | b[j] != b[i] & b[j] - b[i] != j - i & b[j] - b[i] != i - j).

// Queen i is safe with respect to other queens
relation IsSafeQueen(int[] b, int i) ==
	forall(j : (j < 1 | j >= i | AreNotAttackingQueens(b,i,j))).

// Board b[1..n] is consistent if and only if every queen is safe.
relation IsConsistent(int[] b, int n) ==
	//the nested forall formulation does not work!
	//forall(i : (i < 1 | i > n | IsSafeQueen(b,i))).
	forall(i, j: (i < 1 | i > n | j < 1 | j >= i |
		b[j] != b[i] & b[j] - b[i] != j - i & b[j] - b[i] != i - j)).

// There is no solution with prefix b[1..i] and b[i+1] in {1..k}, k <= n.
relation NoSolutionPrefix(int[] b, int n, int i, int k) ==
	// base case: i >= n & b[1..n] is inconsistent
	k <= n & (i >= n & !(IsConsistent(b,n))
	// induction: for any choice of b[i+1] in {1..n}, there is 
	// no solution with prefix b[1..i+1]
	| forall(j: (j < 1 | j > k | b[i+1] != j | NoSolutionPrefix(b,n,i+1,n)))).

relation Bounded(int[] a, int i, int j, int l, int h) ==
	(forall(k : (k < i | k > j | l <= a[k] & a[k] <= h))).

/** FUNCTIONS **/

// Solve n-queens
// @return 	false if there is no solution
// 			true if there is a solution; in such case, the resulting 
//					array b gives a valid solution
bool nQueens(ref int[] b, int n)
	requires dom(b,1,n) & 1 <= n
	ensures (res & IsConsistent(b',n) & Bounded(b',1,n,1,n) | !res & NoSolutionPrefix(b',n,0,n));
{
	return nQueensHelper(b, n, 1);
}

// Back-tracking search algorithm
bool nQueensHelper(ref int[] b, int n, int i)
	requires dom(b,1,n) & 1 <= i <= n+1 & IsConsistent(b,i-1) & Bounded(b',1,i-1,1,n) 
	ensures (res & IsConsistent(b',n) & Bounded(b',1,n,1,n) | !res & NoSolutionPrefix(b',n,i-1,n)) 
				& IdenticalRange(b',b,1,i-1);
{
	if (i == n + 1) // nothing more to search!
		return true;
	else
		return nQueensHelperHelper(b, n, i, 1);
}

bool nQueensHelperHelper(ref int[] b, int n, int i, int j)
	requires dom(b,1,n) & 1 <= i <= n & 1 <= j <= n + 1 
				& IsConsistent(b,i-1) & NoSolutionPrefix(b,n,i-1,j-1)
				& Bounded(b',1,i-1,1,n) 
	ensures (res & IsConsistent(b',n) & Bounded(b',1,n,1,n) | !res & NoSolutionPrefix(b',n,i-1,n))
				& IdenticalRange(b',b,1,i-1);
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

bool IsSafe(int[] b, int n, int i)
	requires dom(b,1,n) & 1 <= i <= n & IsConsistent(b,i-1)
	ensures  (res & IsConsistent(b,i) | !res & NoSolutionPrefix(b,n,i,n));
//{
//	int j = 1;
//	bool result = true;
//	while (j < i) 
//		requires true
//		ensures (!result' | result' & IsConsistent(b,n,i));
//	{
//		int h = b[i] - b[j];
//		if (h == 0 || h == i - j || h == j - i) {
//			result = false;
//			break;
//		}
//		j = j + 1;
//	}
//	return result;
//}

//bool IsSafeHelper(int[] b, int n, int i)
//	requires dom(b,0,n-1) & 0 <= i <= n-1 & IsConsistent(b,i-1)
//	ensures  (!res | res & IsConsistent(b,i));
