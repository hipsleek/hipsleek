/**
 Problem 4 in VSComp 2010: N-Queens
 MAIN ISSUES:
  - PROPAGATION OF PROPERTY: currently cannot prove that if c[1..i] and b[1..i] 
	are the same and b[1..i] is consistent then c[1..i] is also consistent.
  - SPECIFY THE NO-SOLUTION.
  - VERIFICATION SUCCEEDS ... WITHOUT ANY CALLS TO Z3
 @author Vu An Hoa
 @date 24/06/2011
 **/

/** RELATIONS **/

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

// DIFFICULT TO WRITE!!!
relation NoSolution(int n) == true.
	//NoSolutionPrefix(b,0).

// There is no solution with prefix b[1..i]
//relation NoSolutionPrefix(int[] b, int n, int i) ==
//	(i >= n & !IsConsistent(b,n) // base case: i >= n & b[1..n] is inconsistent
	// induction: for any choice of b[i+1] in {1..n}, there is no solution with prefix b[1..i+1]
//	| forall(j: (j < 1 | j > n | b[i+1] != j | NoSolutionPrefix(b,n,i+1)))).

/** FUNCTIONS **/

// Solve n-queens
// @return 	false if there is no solution
// 			true if there is a solution; in such case, the resulting 
//					array b gives a valid solution
bool nQueens(ref int[] b, int n)
	requires dom(b,1,n) & 1 <= n
	ensures (res & IsConsistent(b',n) | !res & NoSolution(n));
{
	return nQueensHelper(b, n, 1);
}

// Back-tracking search algorithm
bool nQueensHelper(ref int[] b, int n, int i)
	requires dom(b,1,n) & 1 <= i <= n+1 & IsConsistent(b,i-1)
	ensures (res & IsConsistent(b',n) | !res & NoSolution(n)) 
				& IdenticalRange(b',b,1,i-1);
{
	if (i == n + 1) // nothing more to search!
		return true;
	else
		return nQueensHelperHelper(b, n, i, 1);
	// 67357
}

bool nQueensHelperHelper(ref int[] b, int n, int i, int j)
	requires dom(b,1,n) & 1 <= i <= n & 1 <= j <= n + 1 & IsConsistent(b,i-1)
	ensures (res & IsConsistent(b',n) | !res & NoSolution(n))
				& IdenticalRange(b',b,1,i-1);
{
	if (j <= n) {
		b[i] = j; // try putting a queen at (i,j)
		//assert IsConsistent(b',i-1);	// we know that b'[1..i-1] = b[1..i-1]
		//assume IsConsistent(b',i-1); 	// but we cannot prove this property!
		if (IsSafe(b,n,i)) {
			if (nQueensHelper(b,n,i+1)) // safe ==> try the next queen
				return true;
			else { 	// cannot find solution by putting queen at (i,j)
					// need to make sure that b[1..i] is not changed
					// after the call nQueensHelper(b,n,i+1)
				//assert IsConsistent(b',i-1); 
				//assume IsConsistent(b',i-1);
				return nQueensHelperHelper(b, n, i, j + 1);
			}
		}
	}
	return false;	// call when j > n i.e. j = n+1 or when (i,j) is not a safe position
}

bool IsSafe(int[] b, int n, int i)
	requires dom(b,1,n) & 1 <= i <= n & IsConsistent(b,i-1)
	ensures  (res & IsConsistent(b,i) | !res);
/*{
	int j = 1;
	bool result = true;
	while (j < i) 
		requires true
		ensures (!result' | result' & IsConsistent(b,n,i));
	{
		int h = b[i] - b[j];
		if (h == 0 || h == i - j || h == j - i) {
			result = false;
			break;
		}
		j = j + 1;
	}
	return result;
}*/

/*bool IsSafeHelper(int[] b, int n, int i)
	requires dom(b,0,n-1) & 0 <= i <= n-1 & IsConsistent(b,i-1)
	ensures  (!res | res & IsConsistent(b,i));*/

