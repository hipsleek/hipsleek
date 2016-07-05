data node {
	int val; 
	node next; 
}

sortHO<v,R:relation(int,int)> == self=null
  or self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) & p!=null
inv true;

