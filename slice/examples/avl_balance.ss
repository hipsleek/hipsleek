data node {
	int val;
	node left;
	node right;
};
		  
avl<h, n, b, s, B> ==
	   self = null & h = 0 & n = 0 & b = 0 & B = {}
	or self::node<v, p, q> * p::avl<h1, n1, b1, s1, B1> * q::avl<h2, n2, b2, s2, B2>
	   & v >= 0
	   & n = 1 + n1 + n2
	   & -1 <= h1 - h2 <= 1 & h = 1 + max(h1, h2) 
	   & b = h1 - h2
	   & s = v + s1 + s2
	   & B = union({v}, B1, B2) & forall (x : (x notin B1 | x <= v)) & forall (x : (x notin B2 | x > v))
	inv n >= 0 & h >= 0 & n >= h & -1 <= b <= 1 & s >= 0 & forall (x : (x notin B | x >= 0)) 
	
Because 
A |- C 
B |- C
----------------
A \/ B |- C

and the invariant is satisfied under the case self = null, we only need to consider the case self != null. 

Automatic slicing:
- Linking variables (v causes s and B grouped together)
- Linking constraints (n >= h (RHS) and b = h1 - h2 (LHS) cause n, h and B grouped together)
    [[n, h, b], [s, B]]
	
	  n = 1 + n1 + n2
	& -1 <= h1 - h2 <= 1 
	& h = 1 + max(h1, h2) 
	& b = h1 - h2
	& n1 >= 0 & n2 >= 0
	& h1 >= 0 & h2 >= 0
	& n1 >= h1 & n2 >= h2
	& -1 <= b1 <= 1 & -1 <= b2 <= 1
	|- n >= 0
	
	  n = 1 + n1 + n2
	& -1 <= h1 - h2 <= 1 
	& h = 1 + max(h1, h2) 
	& b = h1 - h2
	& n1 >= 0 & n2 >= 0
	& h1 >= 0 & h2 >= 0
	& n1 >= h1 & n2 >= h2
	& -1 <= b1 <= 1 & -1 <= b2 <= 1
	|- h >= 0
	
	  n = 1 + n1 + n2
	& -1 <= h1 - h2 <= 1 
	& h = 1 + max(h1, h2) 
	& b = h1 - h2
	& n1 >= 0 & n2 >= 0
	& h1 >= 0 & h2 >= 0
	& n1 >= h1 & n2 >= h2
	& -1 <= b1 <= 1 & -1 <= b2 <= 1
	|- n >= h
	
	  n = 1 + n1 + n2
	& -1 <= h1 - h2 <= 1 
	& h = 1 + max(h1, h2) 
	& b = h1 - h2
	& n1 >= 0 & n2 >= 0
	& h1 >= 0 & h2 >= 0
	& n1 >= h1 & n2 >= h2
	& -1 <= b1 <= 1 & -1 <= b2 <= 1
	|- -1 <= b <= 1

Forced slicing:

Optimal:

		  
		  
