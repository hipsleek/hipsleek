relation is_modified(int[] val, int[] idx, int[] bk, int n, int i) ==
	0 <= idx[i] < n & bk[idx[i]] = i.

relation value_at(int[] val, int[] idx, int[] bk, int n, int i, int v) ==
	0 <= i <= 1000-1 & (is_modified(val, idx, bk, n, i) & val[i] = v | !(is_modified(val, idx, bk, n, i)) & v = 0).

checkentail value_at(val,idx,bk,n,i,v) & u != v |- !(value_at(val,idx,bk,n,i,u)).
