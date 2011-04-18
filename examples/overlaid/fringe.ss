data node {
	int val;
	node left;
	node right;
	node link;
}
/*
lseq<y,n> == self = y & n = 0
          or self::node<_, _, _, q> * q::lseq<y,n1> & n = n1 + 1 //& self!=y
          inv n>=0;

btree<n> == self = null & n = 0
         or self::node<_, l, r, _> * l::btree<n1> * r::btree<n2> & n = 1 + n1 + n2
         inv n>=0;
*/

lseq<y, n, B> == self = y & n = 0 & B = {}
              or self::node<v, _, _, q> * q::lseq<y, n1, B1> & n = n1 + 1 & B = union(B1, {v})
              inv n>=0;

btree<n, B> == self = null & n = 0 & B = {}
            or self::node<v, l, r, _> * l::btree<n1, B1> * r::btree<n2, B2> & n = 1 + n1 + n2 & B = union(union(B1, B2), {v})
            inv n>=0;


node fringelink(node x, node y)
/*
requires x::btree<n>
ensures res::lseq<y,n2> & n2<=n;
//ensures (x::btree<n> & res::lseq<y,_>);
*/

requires x::btree<n,B>
ensures res::lseq<y,n1,B1> & n1 <= n;
//ensures res::lseq<y,n1,_>;

{
	if (x == null) {
		//assume false;
		return y; //new node(0,null,null,y);
	} else if (x.left == null && x.right == null) {
		//assume false;
		x.link = y;
		return x;
	}
	else {
		//assume false;
		node z = fringelink(x.right, y);
		//dprint;
	    node w = fringelink(x.left, z);
		//dprint;
		return append2(w,z);
	}
}

node append(node x, node y)
/*
//requires x::lseq<y,n1> * y::lseq<z,n2>
//ensures res::lseq<z,n> & n <= n1 + n2;
requires x::lseq<y,_> * y::lseq<z,_>
ensures res::lseq<z,_>;
*/

//requires x::lseq<y,_,B1> * y::lseq<z,_,B2>
//ensures res::lseq<z,_,B> & B = union(B1, B2);
//requires x::lseq<y,_,_> * y::lseq<z,_,_>
//ensures res::lseq<z,_,_>;
//requires x::lseq<y,n1,_> * y::lseq<z,n2,_>
//ensures res::lseq<z,n,_> & n <= n1 + n2;
/*
case {
	  x=y -> requires x::lseq<y,n1> * y::lseq<z,n2>
		     ensures res::lseq<z,n1+n2> ;
	x!=y -> requires x::lseq<y,n1> * y::lseq<z,n2>		     
            ensures res::lseq<z,n1+n2> ;
			}
*/
//requires x::lseq<y,n1>
//ensures res::lseq<y,n1> ;
/*

{
	if (x == y) {
		dprint;
		//false;
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
*/
/*
node append2(node x, node y)
requires x::lseq<y,n1> * y::lseq<z,n2>
ensures res::lseq<z,n> & n = n1 + n2;
*/
node append2(node x, node y)
requires x::lseq<y,n1,B1> * y::lseq<z,n2,B2>
ensures res::lseq<z,n,B> & n = n1 + n2 & B=union(B1,B2);

