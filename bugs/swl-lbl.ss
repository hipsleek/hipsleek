data node{
	int val;
	node next;
}


lg<"n":s,"b":M> == true & ["n":self = null & self != s; "b":M = {}] 
	or self::node<_,nxt> * nxt::lg<s,Mnxt> & ["b": M = union(Mnxt,{self}); "n": self != s]
inv true & ["n":self!=s];


