data node {
	int val;
	node next;
}

ll<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll<n-1, S-{v}>;

ll<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll<m, S1> & n=m+1 & S=union(S1, {v}, a, b, c) & R=intersect(a,b,d);

