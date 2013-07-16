data node{
	int val;
	node next;
}


lg<"n":s,"b":M> == true & ["n":self = null & self != s; "b":M = {}] 
	or self::node<_,nxt> * nxt::lg<s,Mnxt> & ["b": M = union(Mnxt,{self}); "n": self != s]
inv ["n":self!=s];

/*
since inv is supposed to contain just pure, why can't
we have:
inv ["n":self!=s];

*/

