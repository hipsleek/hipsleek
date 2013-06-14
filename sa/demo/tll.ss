data node{
	node left;
	node right;
	node next;
};

/* predicate for a tree with chained leaf list */
 tll<ll,lr> = self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>;

