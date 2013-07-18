data node2{
	int val;
	node2 n;
	node2 s;
}

skipll<> == self=null 	or	self::node2<_,p,q> * q::skipll<> * p::lseg<q>;

lseg<q> == 	self=q 	or	self::node2<_,n,null>* n::lseg<q>;
	
HeapPred SLL(node2 a).
HeapPred SLSEG(node2 a,node2 b).
HeapPred SLSEGP(node2 a,node2 b).

bool skip1(node2 l)
//infer[SLL] requires SLL(l) ensures true;
requires l::skipll<> ensures res;

{
	if (l==null) return true;
	else return skip1(l.s) && skip0(l.n,l.s);
}

bool skip0(node2 l, node2 e) 
//infer[SLSEG] requires SLSEG(l,e) ensures true;// res
requires l::lseg<e> ensures res;
{
	if (l == e) return true;
	else if (l==null) return false;
	else  return skip0(l.n, e) && l.s == null;
}


