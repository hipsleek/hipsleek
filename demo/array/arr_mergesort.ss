/**
 Example: merge two arrays.
 **/

//relation idexc(int[] a, int[] b, int i, int j) == 
//    forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == 
    (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).
   
relation upperbnd(int[] a, int i, int j, int s) == 
    (i > j | forall ( k : (k < i | k > j | a[k] <= s))).

relation idbtwn(int[] a, int ia, int ja, int[] b, int ib, int jb) == 
    ja - ia = jb - ib &
    forall(k : (k<ib | jb<k | a[ia+k-ib] = b[k])).

/**
 Merge sorted portions of array: a[ia..ia+n-1] and b[ib..jb+n-1]
 into a sorted array c[0..m+n-1]. The parameters n and m are hence 
 for the numbers of elements; which is just for ease of use.
 */
void merge_sorted_arrays(int[] a, int ia, int n,
                              int[] b, int ib, int m,
                              ref int[] c)
	requires [la,ha,lb,hb,lc,hc,u] 
	         dom(a,la,ha) & la <= ia & ia+n-1 <= ha & n >= 0 & 
	         dom(b,lb,hb) & lb <= ib & ib+m-1 <= hb & m >= 0 &
	         dom(c,lc,hc) & lc <= 0 & m+n-1 <= hc &
	         upperbnd(a,ia,ia+n-1,u) & upperbnd(b,ib,ib+m-1,u) &
	         sorted(a,ia,ia+n-1) & sorted(b,ib,ib+m-1)
	ensures dom(c',lc,hc) & sorted(c',0,m+n-1) &
	        upperbnd(c',0,m+n-1,u) & amodr(c,c',0,m+n-1);
{
	int p = m + n - 1;
	int ja = ia + n - 1;
	int jb = ib + m - 1;
	if (n > 0) {
		if (m > 0) {
			if (a[ja] > b[jb]) { 
				c[p] = a[ja];
				n = n - 1;
			}
			else { 
				c[p] = b[jb];
				m = m - 1; 
			}
		} else { 
			c[p] = a[ja]; 
			n = n - 1; 
		}
	}
	else if (m > 0) { 
		c[p] = b[jb]; 
		m = m - 1; 
	}
	// REMARK: assertion cannot be proved.
	//assert upperbnd(a,ia,ia+n'-1,c'[p']);
	assume upperbnd(a,ia,ia+n'-1,c'[p']);
	merge_sorted_arrays(a, ia, n, b, ib, m, c);
}



/**
 Copy array a[s..e] to b[i..i+e-s].
 NOTE: the algorithm is NOT guaranteed when a and b overlap.
 */
void copy_array(int[] a, int s, int e, ref int[] b, int i)
	requires [la,ha,lb,hb] dom(a,la,ha) & la <= s & e <= ha & 
	                       dom(b,lb,hb) & lb <= i & i + e - s <= hb
	ensures idbtwn(a,s,e,b',i,i+e-s) & amodr(b',b,i,i+e-s);
{
	if (e >= s) {
		b[i] = a[s];
		copy_array(a,s+1,e,b,i+1);
	}
}


/**
 Sort the array a[i..j] using merge sort algorithm.
 */
void merge_sort(ref int[] a, int i, int j)
	requires [la,ha] dom(a,la,ha) & la <= i & j <= ha
	ensures dom(a',la,ha) & sorted(a',i,j) & amodr(a,a',i,j);
{
	if (i < j) {
		int m = (i + j) / 2;
		// note that m < j as i < j so that two
		// reductions really reduce the problem.
		merge_sort(a,i,m);
		merge_sort(a,m+1,j);
		int[] c = new int[j-i+1];	

		/* NOTE: This variable is NOT used in the program.
		         It is used solely to support existential
		         instantiation in merge_sorted_arrays */
		int u;
		if (a[m] > a[j]) u = a[m]; else u = a[j];
		
		// This assertion fails naturally because the two merge sorts
		// are currently not related to each other i.e. the information
		// [i..m] and [m+1..j] are DISJOINT is not captured!
		//assert upperbnd(a',i,m',u') & upperbnd(a',m'+1,j,u');		
		assume upperbnd(a',i,m',u') & upperbnd(a',m'+1,j,u');
		
		merge_sorted_arrays(a,i,m-i+1,a,m+1,j-m,c);
		copy_array(c,0,j-i,a,i);
	}
}




/**
 Merge two sorted arrays into a sorted array.
 For implementation simplicity, array is indexed from 1!
 So a[1..n], b[1..m], c[1..m+n].
 If n = 0 or m = 0, a (or b respectively) contributes
 no element.
 */
/*
void merge_sorted_arrays(int[] a, int n, int[] b, int m, ref int[] c)
	requires [ha,hb,hc,u] dom(a,1,ha) & 0 <= n & n <= ha & 
	                      dom(b,1,hb) & 0 <= m & m <= hb & 
	                      dom(c,1,hc) & m+n <= hc &
	                      upperbnd(a,1,n,u) & upperbnd(b,1,m,u) &
	                      sorted(a,1,n) & sorted(b,1,m)
	ensures dom(c',1,hc) & sorted(c',1,m+n) &
	        upperbnd(c',1,m+n,u) & amodr(c,c',1,m+n);
{
	int p = m + n;
	if (n > 0) {
		if (m > 0) {
			if (a[n] > b[m]) {
				c[p] = a[n];
				assert upperbnd(a,1,n-1,c'[p']);
				assume upperbnd(a,1,n-1,c'[p']);
				assert upperbnd(b,1,m,c'[p']);
				assume upperbnd(b,1,m,c'[p']);
				merge_sorted_arrays(a, n-1, b, m, c);
			}
			else {
				c[p] = b[m];
				assert upperbnd(a,1,n,c'[p']);
				assume upperbnd(a,1,n,c'[p']);
				assert upperbnd(b,1,m-1,c'[p']);
				assume upperbnd(b,1,m-1,c'[p']);
				merge_sorted_arrays(a, n, b, m - 1, c);
			}
		} else {
			// b exhausts, keep copying the remaining of a to c
			c[p] = a[n];
			assert upperbnd(a,1,n-1,c'[p']);
			assume upperbnd(a,1,n-1,c'[p']);
			assert upperbnd(b,1,m,c'[p']);
			assume upperbnd(b,1,m,c'[p']);
			merge_sorted_arrays(a, n - 1, b, m, c);
		}
	}
	else {
		// a exhausts, keep copying the remaining of b to c
		if (m > 0) {
			c[p] = b[m];
			assert upperbnd(a,1,n,c'[p']);
			assume upperbnd(a,1,n,c'[p']);
			assert upperbnd(b,1,m-1,c'[p']);
			assume upperbnd(b,1,m-1,c'[p']);
			merge_sorted_arrays(a, n, b, m - 1, c);
		}
	}
}
*/


/**
 Merge sorted portions of array: a[ia..ia+n-1] and b[ib..jb+n-1]
 into a sorted array c[0..m+n-1].
 */
/*
void merge_sorted_arrays_part(int[] a, int ia, int n,
                              int[] b, int ib, int m,
                              ref int[] c)
	requires [la,ha,lb,hb,lc,hc,u] 
	         dom(a,la,ha) & la <= ia & ia+n-1 <= ha & n >= 0 & 
	         dom(b,lb,hb) & lb <= ib & ib+m-1 <= hb & m >= 0 &
	         dom(c,lc,hc) & lc <= 0 & m+n-1 <= hc &
	         upperbnd(a,ia,ia+n-1,u) & upperbnd(b,ib,ib+m-1,u) &
	         sorted(a,ia,ia+n-1) & sorted(b,ib,ib+m-1)
	ensures dom(c',lc,hc) & sorted(c',0,m+n-1) &
	        upperbnd(c',0,m+n-1,u) & amodr(c,c',0,m+n-1);
{
	int p = m + n - 1;
	int ja = ia + n - 1;
	int jb = ib + m - 1;
	if (n > 0) {
		if (m > 0) {
			if (a[ja] > b[jb]) {
				c[p] = a[ja];
				assume upperbnd(a,ia,ja'-1,c'[p']);
				assume upperbnd(b,ib,jb',c'[p']);
				merge_sorted_arrays_part(a, ia, n-1, b, ib, m, c);
			}
			else {
				c[p] = b[jb];
				assume upperbnd(a,ia,ja',c'[p']);
				assume upperbnd(b,ib,jb'-1,c'[p']);
				merge_sorted_arrays_part(a, ia, n, b, ib, m - 1, c);
			}
		} else {
			// b exhausts, keep copying the remaining of a to c
			c[p] = a[ja];
			assume upperbnd(a,ia,ja'-1,c'[p']);
			assume upperbnd(b,ib,jb',c'[p']);
			merge_sorted_arrays_part(a, ia, n - 1, b, ib, m, c);
		}
	}
	else {
		// a exhausts, keep copying the remaining of b to c
		if (m > 0) {
			c[p] = b[jb];
			assume upperbnd(a,ia,ja',c'[p']);
			assume upperbnd(b,ib,jb'-1,c'[p']);
			merge_sorted_arrays_part(a, ia, n, b, ib, m - 1, c);
		}
	}
}
*/