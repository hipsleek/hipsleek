/**
 Problem 4 in VSComp 2010: N-Queens
 @author Vu An Hoa
 @date 24/06/2011
 **/

relation IsConsistent(int[] b, int n) == true.

relation NoSolution(int n) == true.

// solve n-queens, return false if there is no solution
bool nqueens(int[] b, int n)
	requires dom(b,0,n-1)
	ensures (res & IsConsistent(b,n) | !res & NoSolution(n))
{
	
}
