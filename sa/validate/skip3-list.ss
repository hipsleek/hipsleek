data node3{
	int val;
	node3 n1;
	node3 n2;
	node3 n3;	
}

skipll3<> == self=null or self::node3<_,null,n2,n3> * n2::skipll2<n3> * n3::skipll3<>;

skipll2<q> == self=q or self::node3<_,n1,n2,null> * n2::skipll2<q> * n1::lseg<n2>;

//lseg2<q> == seff=q or self::node3<_,_,n2,null> * n2::lseg2<q>;

lseg<q> == self=q or self::node3<_,n1,null,null> * n1::lseg<q>;
	
HeapPred H1(node3 a,node3@NI b).
HeapPred H2(node3 a,node3@NI b).
HeapPred H3(node3 a).

bool skip2(node3 l)
infer[H3] requires H3(l) ensures res;
	/* requires l::skipll3<> */
	/* ensures res; */
{
	if (l==null) return true;
	else return skip2(l.n3) && l.n1==null && skip1(l.n2, l.n3);
}

bool skip1(node3 l, node3 e)
infer[H2] requires H2(l,e) ensures res;
	/* requires l::skipll2<e> */
	/* ensures res; */
{
	if (l==e) return true;
	else return (l!=e) && skip0(l.n1, l.n2) && l.n3 == null && skip1(l.n2, e);
}

bool skip0(node3 l, node3 e) 
infer[H1] requires H1(l,e) ensures res;
	/* requires l::lseg<e> */
	/* ensures res; */
{
	if (l == e) return true;
    else return (l!=null) && l.n2 == null && l.n3 == null && skip0(l.n1, e);
}


