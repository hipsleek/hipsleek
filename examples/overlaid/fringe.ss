data node {
	int val;
	node left;
	node right;
	node link;
}

lseq<y,n> == self = y & n = 0
          or self::node<_, _, _, q> * q::lseq<y,n1> & n = n1 + 1
          inv n>=0;


btree<n> == self = null & n = 0
         or self::node<_, l, r, _> * l::btree<n1> * r::btree<n2> & n = 1 + n1 + n2
         inv n>=0;

node fringelink(node x, node y)
requires x::btree<n>
ensures res::lseq<y,_>;
{
	if (x == null)
		return new node(0,null,null,y);
	else if (x.left == null && x.right == null) {
		x.link = y;
		return x;
	}
	else {
		node z = fringelink(x.right, y);
		//dprint;
	    node w = fringelink(x.left, z);
		//dprint;
		return append(w,z);
	}
}

node append(node x, node y)
//requires x::lseq<y,n1> * y::lseq<z,n2>
//ensures res::lseq<z,n> & n <= n1 + n2;
requires x::lseq<y,_> * y::lseq<z,_>
ensures res::lseq<z,_>;
{
	if (x == y) {
		//dprint;
		return y;
	}
	else {
		node w = append(x.link, y);
		//assert w::lseq<z,_>;
		//dprint;
		x.link = w;
		return x;
	}
}
/*
node append2(node x, node y)
requires x::lseq<y,n1> * y::lseq<z,n2>
ensures res::lseq<z,n> & n = n1 + n2;
{
	return x;
}
*/