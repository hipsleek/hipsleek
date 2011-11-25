// Natural numbers encoded using linked data structure
data S {
	S predecessor;
}.

// S --> S --> S --> ... --> S --> null
pred nat<m> == self = null & m = 0
	or self::S<x> * x::nat<m-1> & m > 0.

// self and x points to natural numbers of the same abstract value
pred nateq<x> == self = null & x = null
	or self::S<n1> * x::S<n2> * n1::nateq<n2>.

// a represents the natural number ma & b is equal to a
// then b must represents the same number
checkentail a::nat<ma> * b::nateq<a> |- b::nat<ma>.

// self represents the sum of natural numbers pointed by x and y
// define recursively by: 
// x + y := y if x = 0
//       := S(x'+y) if x = S x'
pred plus<x,y> == self::nateq<y> & x = null
	or self::S<n2> * x::S<n1> * n2::plus<n1,y>.

// if a-->[ma] & b-->[mb] & c = a+b then c-->[ma+mb]
checkentail a::nat<ma> * b::nat<mb> * c::plus<a,b> |- c::nat<ma+mb>.



// Linked list
data node {
	int val;
	node next;
}.

//lseg<b> == self = b
//	or self::node<v,n> * n::lseg<b>;

//lleq<x> == self = x
//	or self::node<v,n1> * x::node<v,n2> * n1::lleq<n2>;


