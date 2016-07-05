data node {
	int val;
	node next;
}

// lists with bag of elements

ll<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll<m, Sr> & n=m+1 & S=Sr bag_union {v}
	inv n>=0;

node add_first(node x, int v)
	requires x::ll<n, S> 
	ensures res::ll<n+1, S bag_union {v}>;


node remove(node x, int v)
	requires x::ll<n, S>
	ensures res::ll<n-1, S-{v}> & v in S
		 or res::ll<m, S> & v not_in S;

res::ll<m, Sr> & (m=n-1 & Sr=S-{v} & v in S \/ m=n & Sr=S & v not_in S)

// following won't work

node remove(node x, int v)
	requires x::ll<n, S> & v in S
	ensures res::ll<n-1, S-{v}>;
	requires x::ll<n, S> & v not_in S
	ensures res::ll<n, S>;

//this won't work
node remove_copy(node x, int v, node y)
	requires x::ll<n, S> & v not_in S
	ensures x::ll<n, S>;
	requires x::ll<n, S> * y::ll<m, S1> & v in S
	ensures x::ll<n-1, S-{v}> * y::ll<m+1, S1+{v}>;


node remove_copy(node x, int v, node y)
	requires 


// sorted lists

sortl<n, mx, mn, S> == self::node<v, null> & n=1 & mx=mn=v & S={v}
	or self::node<v, r> * r::sortl<m, mmx, mmn, Sr> & n=m+1 & v<=mmx & S=Sr bag_union {v} 
	inv n>=0 & mx<=mn & S != {};


node sort(node x)
	requires x::ll<n, S> & n>0
	ensures res::sortl<n, mx, mn, S> & (forall s in S. mn<=s<=mx)
