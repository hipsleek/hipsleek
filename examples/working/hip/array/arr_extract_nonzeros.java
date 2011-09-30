/**
 * Count how many nonzeros elements in an array, allocate
 * the exact memory and fill the array with those non-zeros
 * elements.
 * 
 * Reference:
 * 1) Extract non-zero values from an array
 * http://proval.lri.fr/gallery/muller.en.html
 * 2) Filter elements of an array
 * http://proval.lri.fr/gallery/MullerJava.en.html
 * 
 * @author Vu An Hoa
 */

// Need induction to show that n >= 0. Currently, our induction
// capability does not work!
relation numnonzeros(int[] a, int i, int j, int n) ==
	(i > j & n = 0 | i <= j & (a[j] = 0 & numnonzeros(a,i,j-1,n) | 
		a[j] != 0 & numnonzeros(a,i,j-1,n-1))) & n >= 0.

relation alldiff(int[] a, int x, int i, int j) ==
	forall(k : k < i | k > j | a[k] != x).
	
// Extract the non-zero elements of a into the array b. Allocate
// sufficient memory for b.
void extract_nonzeros(int[] a, int i, int j, ref int[] b)
	requires [al,ah] dom(a,al,ah) & al <= i & j <= ah
	ensures true;
{
	int n = count_nonzeros(a, i, j);
	b = new int[n];
	copy_nonzeros(a, i, j, b, n);
}

// Count the number of non-zero elements in a[i..j]
int count_nonzeros(int[] a, int i, int j)
	requires [al,ah] dom(a,al,ah) & al <= i & j <= ah
	ensures numnonzeros(a,i,j,res);
{
	if (i > j)
		return 0;
	if (a[j] != 0)
		return 1 + count_nonzeros(a,i,j-1);
	else
		return count_nonzeros(a,i,j-1);
}

// Copy the non-zero elements from a[i..j] to b[1..n] given that
// we already know the number of non-zero elements is n.
void copy_nonzeros(int[] a, int i, int j, ref int[] b, int n)
	requires [al,ah,bh] dom(a,al,ah) & al <= i & j <= ah & 0 <= n &
						numnonzeros(a,i,j,n) & dom(b,0,bh) & n - 1 <= bh
	ensures amodr(b,b',0,n-1) & alldiff(b',0,0,n-1);
{
	if (i <= j) {
		if (a[j] != 0) {
			b[n - 1] = a[j]; // challenge: show that this assignment is safe!
			n = n - 1;
		}
		copy_nonzeros(a, i, j - 1, b, n);
	} else {
		assert n = 0;
	}
}
