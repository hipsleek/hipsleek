data node{
	int val;
	node next;
}

/*
ll<M> == self = null & M = {}
	or self::node<_,nxt> * nxt::ll<Mnxt> & M = union(Mnxt,{self})
inv forall(x: x notin M | x != null);
*/

lg<s,n> == self = null &n=0 & self != s
     or self::node<_,nxt> * nxt::lg<s,n1> 
             & n=n1+1  & self != s
//inv forall(x: x notin M | (x != null & x != s));
inv self!=s & n>=0;

/*
ls<p,M> == self = p & M = {}
	or self::node<_,nxt> * nxt::ls<p,M1> & self != p & M = union({self},M1)
inv true;
*/

