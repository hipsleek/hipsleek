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

Parsing file "bug-lbl-1.ss" by default parser...
File "bug-lbl-1.ss", line 9, characters 4-5
 --error: Stream.Error("[exl_pure] expected after OSQUARE (in [cexp_w])")
 at:(Program not linked with -g, cannot print stack backtrace)

*/

