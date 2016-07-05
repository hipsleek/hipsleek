data node {
	int val;
	node next;
}

ll<n> == self = null & n = 0
	or self::node<v, r> * r::ll<m> & n = m + 1;

data node2 {
	int val;
	node2 left;
	node2 right;
}

tree<n> == self = null & n = 0
	or self::node2<v, l, r> * l::tree<n1> * r::tree<n2> & n = 1 + n1 + n2;

/* tree2<n, h> */

tree2<n, h> == self = null & n = 0 & h = 0
	or self::node2<v, l, r> * l::tree2<n1, h1> * r::tree2<n2, h2> 
		& n = 1 + n1 + n2 & tmp = max(h1, h2) & h = tmp + 1 & 0 <= n1 - n2 <= 1;
