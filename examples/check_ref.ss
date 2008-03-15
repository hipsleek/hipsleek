data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

void test(ref node x)
	requires x::ll<n> ensures x'=null;
{
	if (x!=null) {
	//dprint;
		x = x.next;
	//dprint;
	//debug on;
		//assert x'!=null;
		//assert x'::node<_,_>;
		//assert x'::ll<_>;
	//debug off;


		test(x);
		//assert x'!=null;
		//assert 0>1;
	}
}
