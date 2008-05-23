data node {
 	int val;
	node next;
}.

pred ll<n,u,sm,lg> == self=null & n=0 &  sm<=lg & u=1
        or self::node<v, null> &  n=1 & sm<=v<=lg & u=2
	//or self::node<v, null> & n=1 & sm<=v<=lg & u=1
        or self::node<v, q> * q::ll<n-1,_,sm,lg> & q!=null  &  sm<=v<=lg & u=2
        inv n>=0 & sm<=lg.
 
pred ll2<n,u,sm,lg> == self=null & n=0 & u=1 & sm<=lg
        or self::node<v, q> * q::ll2<n-1,_,sm,lg> & u=3 & sm<=v<=lg
        inv n>=0 & sm<=lg.
 
checkentail x::node<w,q> * q::ll<a,b,sm,lg> & sm<=w<=lg & q!=null //& q=null
	|- (exists d: x::ll<c,d,s2,l2>).  
//	|- x::ll<c,d,s2,l2>.
// 	|- x::ll<n,u,sm,lg>.
print residue.

