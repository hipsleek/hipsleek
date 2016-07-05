data node {
	int val;
	node next;
}

ll0<> == self=null
	or self::node<_, r> * r::ll0<>;

ll1<n> == self=null & n=0
	or self::node<_, r> * r::ll1<n-1>
	inv n>=0;

ll2<n> == self=null & n=0
	or self::node<_, r> * r::ll2<n-1>
	inv n>=0;

ll_tail<tx> == self=null
	or self::node<_, null> & tx=self
	or self::node<_, r> * r::ll_tail<tx> & r!=null;

lseg<p> == self=p
	or self::node<_, r> * r::lseg<p>;

/*
equiv lltail(node x)
	requires x::ll_tail<tx>
	ensures x::lseg<tx> * tx::node<_, null>;

void test2(node x)
	requires x::ll_tail<tx> & x!=null
	ensures x::lseg<tx> * tx::node<_, q> & q=null;
{
}
*/
lemma a(node x)
	requires x::ll0<>
	ensures x::ll1<n>;
//	requires x::ll1<n>
//	ensures x::ll2<n>;

/*
//{
//	if (x!=null) a(x.next);
//}


equiv b1(node x)
	requires x::ll2<n>
	ensures x::ll1<n>;
//{
//	if (x!=null) b1(x.next);
//}

reverse b2(node x)
	requires x::ll0<>
	ensures x::ll2<n>;

void test(node x) 
	requires x::ll1<n>
	ensures x::ll2<n>;
	requires x::ll2<n>
	ensures x::ll0<>;
{
}

/*
void test2(node x)
	requires x::ll0<>
	ensures x::ll1<n>;
{
}

bnd<n, s, l> == self=null & n=0
	or self::node<d, p> * p::bnd<n1, s1, l1> & n=n1+1 & s<=d<=l & s<=s1 & l1<=l
	inv n>=0;

sortl<n, i, j> == self::node<d, null> & n=1 & i=j=d
	or self::node<d, p> * p::sortl<n1,i1,j1> & n=n1+1 & i=d<=i1 & j=j1
	inv n>=0;


equiv b(node x)
	requires x::ll1<n>
	ensures x::bnd<n, _, _>;
{
	if (x!=null) {
		b(x.next);
		//assume false;
	}
}

void test1(node x)
	requires x::bnd<n, s, l>
	ensures x::ll1<n>;
{
}

void id3b(node x, node p, node r, int n)
        //requires x::lseg<p, n> & x!=p
        //ensures r::lseg<p,j> * x::lseg<r, i> & n=i+j ;
        requires x::lseg<r, i> * r::lseg<p, j> & n=i+j & x!=p
        ensures x::lseg<p, n>;
{
        if (x == r)
        {
                skip();
        }
        else {
                bind x to (v, z) in
                { if (z==p) { 

					assert z=r;

					skip();
                    assume false;
                  }
                  else 
					id3b(z, p ,r,n-1); //, n-1);
                }
        }
}

void skip() requires true ensures true;
*/

/*
lseg1<p> == self=p
	or self::node<_, r> * r::lseg1<p>;

void id3c(node x, node p, node r)
	requires x::lseg<r, i> * r::lseg<p, j>
	ensures x::lseg<p, n> & n=i+j;
{
	if (x!=r) {
		id3c(x.next, p, r);
		//dprint;
		assume false;
	}
	else {
		assert x=r;
		assert i=0;
		//assume false;
	}
}

lemma c(node x)
	requires x::ll0<>
	ensures x::ll2<n>;
{
}
*/

