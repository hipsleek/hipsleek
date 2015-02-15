
data node {
	int val; 
	node next;	
}

HeapPred H(node x, int v). // non-ptrs are @NI by default
  PostPred G(node x, node y, int v). // non-ptrs are @NI by default

ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});

node delete1(node x, int a)
  infer [H,G]  requires  H(x,a)  ensures G(x,res,a);
//	requires x::ll1<S>  
//	ensures res::ll1<S1> & ((a notin S | S=union(S1, {a})) | S = S1);
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}
