data node{
	int val;
	node next;
}

/*
ll<M> == self = null & M = {}
	or self::node<_,nxt> * nxt::ll<Mnxt> & M = union(Mnxt,{self})
inv forall(x: x notin M | x != null);
*/

lg<s,M> == self = null & M = {} & self != s
     or self::node<_,nxt> * nxt::lg<s,Mnxt> 
             & M = union(Mnxt,{self}) & self != s
//inv forall(x: x notin M | (x != null & x != s));
inv self!=s;

/*
ls<p,M> == self = p & M = {}
	or self::node<_,nxt> * nxt::ls<p,M1> & self != p & M = union({self},M1)
inv true;
*/

