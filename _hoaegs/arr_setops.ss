/**
 Example: using array to represents sets data structure.
 **/

// s is a set with n elements
relation isset(int[] s, int n) == 0 <= n &
     forall(i,j: (i < 0 | i >= n | j < 0 | j >= n | i = j |
           i != j & s[i] != s[j])).

relation idbwn(int[] s, int[] t, int i, int j) ==
     forall(k : (k < i | k > j | s[k] = t[k])).

// s is a subset of t
relation issubset(int[] s, int n, int[] t, int nt) ==
     //(n = 0 | n > 0 & issubset(s,n-1,t,nt) & member(t,0,nt-1,s[n-1])).
     forall(i : (i < 0 | i >= n | member(t,0,nt-1,s[i]))).

// u is the union of a & b
relation isunion(int[] u, int n, int[] a, int na, int[] b, int nb) ==
     issubset(a,na,u,n) & issubset(b,nb,u,n).

// x in s where |s| = n
relation member(int[] s, int i, int j, int x) == 
        exists(k: i <= k & k <= j & s[k] = x).

bool contain(int[] S, int i, int j, int x)
	requires true
        ensures (res | !(member(S,i,j,x))) & (!res | member(S,i,j,x));
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
	requires isset(S,n)
	ensures isset(S',n') & member(S',0,n'-1,x) & idbwn(S,S',0,n-1) & issubset(S,n,S',n');
{
	if (!contain(S,0,n-1,x))
	{
		S[n] = x;
		n = n + 1;
                assert (!(idbwn(S,S',0,n-1)) | n' < n | issubset(S,n,S',n'));
                assume (!(idbwn(S,S',0,n-1)) | n' < n | issubset(S,n,S',n'));
	}
}

/**
 Get the index of an element
 **/
int getindex(int[] S, int i, int j, int x)
	requires true
	ensures (res = -1 & !(member(S,i,j,x)) | i <= res & res <= j & S[res] = x);
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
	requires isset(S,n)
	ensures !(member(S',0,n'-1,x));
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
void unionsets(ref int[] S, ref int n, int[] T, int nT)
	requires isset(S,n) & isset(T,nT)
	ensures isset(S',n') & isunion(S',n',S,n,T,nT);
{
	if (nT > 0)
	{
		unionsets(S,n,T,nT-1);
                insert(S,n,T[nT-1]);
	}
}

/**
 Modify the pair (S,n) to get the set S Intersect T
 **/
void intersectsets(ref int[] S, ref int n, int[] T, int nT)
	requires isset(S,n) & isset(T,nT)
	ensures isset(S',n') & issubset(S',n,S,n) & issubset(S',n,T,nT);
{
 if (n > 0)
 {
  int k = n-1;
  int t = S[n-1];
  intersectsets(S,k,T,nT); // take intersection of n-1 elements
  n = k;
  if (contain(T,0,nT-1,t)) insert(S,n,t);
 }
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
