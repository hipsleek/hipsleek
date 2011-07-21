/** If the sparse array contains three elements x y z, at index
 *  a b c respectively, then the three arrays look like this:
 *  
 *               b     a      c
 * values +-----+-+---+-+----+-+----+
 *        |     |y|   |x|    |z|    |
 *        +-----+-+---+-+----+-+----+
 *
 * index  +-----+-+---+-+----+-+----+
 *        |     |1|   |0|    |2|    |
 *        +-----+-+---+-+----+-+----+
 *
 *         0 1 2  n=3
 * back   +-+-+-+-------------------+
 *        |a|b|c|                   |
 *        +-+-+-+-------------------+
 *        
 * Reference:
 * Sparse Arrays in Why3
 * http://proval.lri.fr/gallery/vacid_0_sparse_array.en.html
 *
 * @author Vu An Hoa
 */

// Define MAXLEN = 1000
data SparseArray {	
	int[] values;
	int[] index;
	int[] back;
	int n;
}

relation dom(int[] a, int i, int j) == true.

relation bounded(int[] a, int i, int j, int low, int high) ==
	forall(k : k < i | k > j | low <= a[k] <= high).
	
relation is_modified(int[] val, int[] idx, int[] bk, int n, int i) ==
	0 <= idx[i] < n & bk[idx[i]] = i.

relation value_at(int[] val, int[] idx, int[] bk, int n, int i, int v) ==
	0 <= i <= 1000-1 & (is_modified(val, idx, bk, n, i) & v = val[i] | 
							!(is_modified(val, idx, bk, n, i)) & v = 0).
	// this property is provable in sleek!
	//forall(u : u = v | !(value_at(val,idx,bk,n,i,u))).
			
relation idexc(int[] val1, int[] idx1, int[] bk1, int n1, 
			int[] val2, int[] idx2, int[] bk2, int n2, int i) ==
	forall(k : k = i | 
		forall(h : !(value_at(val1,idx1,bk1,n1,k,h)) | value_at(val2,idx2,bk2,n2,k,h)) &
		forall(t : !(value_at(val2,idx2,bk2,n2,k,t)) | value_at(val1,idx1,bk1,n1,k,t))).
	
void harness()
	requires true ensures true;
{
	SparseArray a = create(10);
	SparseArray b = create(20);
	int a5 = get(a, 5);
	int b7 = get(b, 7);
	assert a5' = 0 & b7' = 0;
	setsa(a, 5, 1);
	setsa(b, 7, 2);
	a5 = get(a, 5);
	b7 = get(b, 7);
	assert a5' = 1 & b7' = 2;
	int a0 = get(a, 0);
	int b0 = get(b, 0);
	assert a0' = 0 & b0' = 0;
}


SparseArray create(int sz)
	requires sz >= 0
	ensures res::SparseArray<val,idx,bk,0> & dom(val,0,1000-1) 
		& dom(idx,0,1000-1) & dom(bk,0,1000-1);
{
	int[] values = new int[1000];
	int[] index = new int[1000];
	int[] back = new int[1000];
	return new SparseArray(values, index, back, 0);
}


int get(SparseArray a, int i)
	requires a::SparseArray<val,idx,bk,n>@I & dom(val,0,1000-1) 
			& dom(idx,0,1000-1) & dom(bk,0,1000-1)
			& 0 <= n <= 1000 - 1 & 0 <= i <= 1000-1
			& bounded(bk,0,n-1,0,1000-1)
	ensures value_at(val,idx,bk,n,i,res);
{
	int[] idx = a.index;
	int[] back = a.back;
	if (idx[i] >= 0 && idx[i] < a.n) {
		if (back[idx[i]] == i) {
			int[] val = a.values;
			return val[i];
		}
	}
	return 0;
}


void setsa(SparseArray a, int i, int v)
	requires a::SparseArray<val,idx,bk,n> & dom(val,0,1000-1) 
				& dom(idx,0,1000-1) & dom(bk,0,1000-1)
				& 0 <= n <= 1000 - 1 & bounded(bk,0,n-1,0,1000-1)
				& 0 <= i <= 1000-1
	ensures a::SparseArray<valr,idxr,bkr,nr> & dom(valr,0,1000-1) 
				& dom(idxr,0,1000-1) & dom(bkr,0,1000-1)
				& 0 <= nr <= 1000 - 1
				& (is_modified(val,idx,bk,n,i) & nr = n | 
						!(is_modified(val,idx,bk,n,i)) & nr = n + 1)
				& bounded(bkr,0,nr-1,0,1000-1)
				& value_at(valr,idxr,bkr,nr,i,v)
				& idexc(val,idx,bk,n,valr,idxr,bkr,nr,i);
{
	int[] val = a.values;
	int[] idx = a.index;
	int[] bk = a.back;
	val[i] = v;
	if (idx[i] >= a.n || idx[i] < 0) {
//		assert(n < MAXLEN); // (*), see Verification Tasks
		idx[i] = a.n;
		bk[a.n] = i;
		a.n = a.n + 1;
	} else if (bk[idx[i]] != i) {
//		assert(n < MAXLEN); // (*), see Verification Tasks
		idx[i] = a.n;
		bk[a.n] = i;
		a.n = a.n + 1;
	}
	a.values = val;
	a.index = idx;
	a.back = bk;
}