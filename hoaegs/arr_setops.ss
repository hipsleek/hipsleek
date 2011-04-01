/**
 Example: using array to represents sets data structure.
 **/

// s is a set with n elements
//relation isset(int[] s, int n) == forall(i,j: (i < 0 | i >= n | j < 0 | j >= n | i = j | i != j & a[i] != a[j])).

// x in s where |s| = n
relation eps(int[] s, int i, int j, int x) == exists(k: i <= k & k <= j & s[k] = x).

bool contain(int[] S, int i, int j, int x)
	requires true
	ensures (!res | eps(S,i,j,x));
{
	if (i <= j)
	{
		if (S[i] == x)
			return true;
		else
			return contain(S,i+1,j,x);
	}
	else
		return false;
}

/**
 Modify the pair (S,n) to get the set S U {x}
 **/
void insert(ref int[] S, ref int n, int x)
	requires true
	ensures true 
{
	if (!contain(S,n,x))
	{
		S[n] = x;
		n = n + 1;
	}
}

/**
 Get the index of an element
 **/
int getindex(int[] S, int i, int j, int x)
	requires true
	ensures (res = -1 | i <= res & res <= j & S[res] = x);
{
	if (i > j)
		return -1;
	else if (S[i] == x)
		return i;
	else 
		return getindex(S,i+1,j,x);
}

/**
 Modify the pair (S,n) to get the set S \ {x}
 **/
void remove(ref int[] S, ref int n, int x)
	requires true
	ensures true
{
	int k = getindex(S,0,n-1,x);
	if (k != -1)
	{
		S[k] = S[n-1];
		n = n - 1;
	}
}

/**
 Modify the pair (S,n) to get the set S U T
 **/
void union(ref int[] S, ref int n, int[] T, int nT)
	requires true
	ensures true;
{
	if (nT > 0)
	{
		insert(S,n,T[nT-1]);
		union(S,n,T,nT-1,B);
	}
}

/**
 Modify the pair (S,n) to get the set S Intersect T
 **/
void intersect(ref int[] S, ref int n, int[] T, int nT)
	requires true
	ensures 
{
	if (nT == 0)
	{
		n = 0;
	}
	else 
}

/* data Set {
	int card;    // cardinality
	int[] elms;  // the elements in this set, located at elems[0..card-1]
}

Set empty()
	requires true 
	ensures res::Set<v,_> & v = 0;
{
	Set tmp;
	int[] a;
	tmp = new Set(0,a);
	return tmp;
}

bool setcontains(Set S, int x)
	requires S::Set<n,a>
        ensures (!res | eps(a,0,n-1,x));
{
        return arraycontain(S.elms,0,S.card - 1,x);
}

void insert(Set S, int x)
	requires true
	ensures S::Set<n,a> & isset(a,n);
{

} */
