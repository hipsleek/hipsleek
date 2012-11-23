data node {
	int val;
	node left;
	node right;
}

/*		  
avl<h, n, b, s, B, L> ==
	   self = null & h = 0 & n = 0 & b = 0 & s = 0 & B = {} & L = []
    or self::node<v, p, q> * p::avl<h1, n1, b1, s1, B1, L1> * q::avl<h2, n2, b2, s2, B2, L2> &
	    v >= 0 &
	    n = 1 + n1 + n2 &
	    -1 <= h1 - h2 <= 1 & h = 1 + max(h1, h2) &
	    $:b = h1 - h2 &
	    s = $:v + s1 + s2 &
	    B = union({v}, B1, B2) & forall (x : (x notin B1 | x <= v)) & forall (x : (x notin B2 | x > v)) &
	    L = L1:::v:::L2
	inv n >= 0 & 
        h >= 0 & 
        $:n >= h & 
        -1 <= b <= 1 & 
        s >= 0 & 
        forall (x : (x notin B | x >= 0)) & 
        forall (x : (x notin L | x >= 0)) &
        $:L = bag(B) &
        $:|B| = n 
*/

avl<h, n, b, s> ==
	   self = null & h = 0 & n = 0 & b = 0 & s = 0 
    or self::node<v, p, q> * p::avl<h1, n1, b1, s1> * q::avl<h2, n2, b2, s2> &
	    v >= 0 &
	    n = 1 + n1 + n2 &
	    -1 <= h1 - h2 <= 1 & h = 1 + max(h1, h2) &
	    b = h1 - h2 &
	    s = v + s1 + s2
	    /*B = union({v}, B1, B2) & forall (x1 : (x1 notin B1 | x1 <= v)) & forall (x2 : (x2 notin B2 | x2 > v))*/
	inv n >= 0 &
        h >= 0 &
        n >= h &
        -1 <= b <= 1 &
        s >= 0;
        /*forall (xb : (xb notin B | xb >= 0));*/

int size (node x)
requires x::avl<h, n, b, s>
ensures x::avl<h, n, b, s> & res = n;
{
	if (x == null)
		return 0;
	else
		return 1 + size(x.left) + size(x.right);
}
