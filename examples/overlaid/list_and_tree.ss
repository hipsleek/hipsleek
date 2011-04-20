data node {
	int val;
	node next;
	node pll;
	node left;
	node right;
	node ptree;
}

tree<n,p>
	== self = null & m = 0
	or self::node<_,_,_,l,r,p> * l::tree<n1,p1> * r::tree<n2,p2> & n = 1 + n1 + n2 & p1 = self & p2 = self
	inv n >= 0;

ll<n,p>
	== self = null & n = 0
	or self::node<_,q,p,_,_,_> * q::ll<n1,p1> & n = 1 + n1 & p1 = self
	inv n >= 0;



