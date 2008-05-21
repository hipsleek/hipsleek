data node {
 	int val;
	node next;
}.

/*
pred ll<n,u,sm,lg> == self=null & n=0 &  sm<=lg & u=1
        or self::node<v, null> &  n=1 & sm<=v<=lg & u=1
        or self::node<v, q> * q::ll<n-1,_,sm,lg> & q!=null &  sm<=v<=lg & u=1
        inv n>=0 & sm<=lg.
*/ 
pred ll2<n,u> == self=null & n=0 & u=1 
        or self::node<v, q> * q::ll2<n-1,_> & u=3 & (v=2 | v=4)
        inv n>=0.
pred ll3<n,u> == self=null & n=0 & u=1 
        or self::node<v, q> * q::ll3<n-1,_> & u=3+n & v=4
        inv n>=0.
/* 
checkentail x::node<w,q>*q::ll<a,b,sm,lg> & sm<=w<=lg & q!=null 
	|- (exists d: x::ll<c,d,s2,l2>).
print residue.
checkentail x::node<w,r>*r::node<w,q>*q::ll2<a,b,sm,lg> & sm<=w<=lg & q!=null 
	|- (exists c: x::ll2<c,d,s2,l2> & c>=1).
checkentail x::node<w,r>*r::node<w,q>*q::ll2<a,b> & w=4
	|- (exists c:x::ll2<c,d> & c>=1).
print residue.
checkentail x::node<w,q>*q::ll2<a,b> & w=4
	|- x::ll2<c,d> & c>=1.
print residue.
checkentail x::node<w,r>*r::node<w,q>*q::ll2<a,b> & w=4
	|- (exists c:x::ll2<c,d> & c>=1).
print residue.
*/
checkentail x::node<w,r>*r::node<w,q>*q::ll2<a,b> & w=4
	|- x::ll2<c,d> & c>=1.
print residue.


