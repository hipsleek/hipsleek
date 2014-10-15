data node2{
	int val;
	node2 n;
	node2 s;
}

skipll<> == self=null 	or	self::node2<_,p,q> * q::skipll<> * p::lseg<q>;

lseg<q> == 	self=q 	or	self::node2<_,n,null>* n::lseg<q>;
	
HeapPred H1(node2 a).
HeapPred H2(node2 a,node2@NI b).
//HeapPred H2P(node2 a,node2 b).


bool skip1(node2 l)
infer[H1] requires H1(l) ensures res;
//requires l::skipll<> ensures res;

{
	if (l==null) return true;
	else return skip1(l.s) && skip0(l.n,l.s);
}



bool skip0(node2 l, node2 e) 
infer[H2] requires H2(l,e) ensures res;
//requires l::lseg<e> ensures res;
{
	if (l == e) return true;
        else return (l!=null) && l.s == null && skip0(l.n, e);
        //else if (l==null) return false;
        //else if (l.s!=null) return false;
        //else return skip0(l.n, e);
}


