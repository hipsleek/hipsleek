data node2{
	int val;
	node2 n;
	node2 s;
}

skipll<> == self=null 	or	self::node2<_,p,q> * q::skipll<> * p::lseg<q>;

lseg<q> == 	self=q 	or	self::node2<_,n,null>* n::lseg<q>;
	
HeapPred SLL(node2 a).
PostPred G(node2 a).
HeapPred SLSEG(node2 a,node2 b).
HeapPred SLSEGP(node2 a,node2 b).

bool skip1(node2 l)
//infer[SLL,G] requires SLL(l) ensures G(l) & res;
requires l::skipll<> ensures res;

{
	if (l==null) return true;
	else return skip1(l.s) && skip0(l.n,l.s);
}

bool skip0(node2 l, node2 e) 
//infer[SLSEG] requires SLSEG(l,e) ensures res;
requires l::lseg<e> ensures l::lseg<e> & res;
{
	if (l == e) return true;
	else if (l==null) return false;
	else  return  l.s == null;
}

/*
[ SLL(l_961) ::= 
 n_22_959::lseg<v_node2_22_815'>@M[LHSCase] * HP_938(v_node2_22_815') * 
 SLL(s_22_958) * l_961::node2<val_22_957,n_22_959,s_22_958>@M
 or emp&l_961=null
 ,
 G(l_964) ::= 
 emp&l_964=null
 or l_964::node2<val_22_915,n_22_916,s_22_917>@M * G(s_22_917) * 
    HP_938(s_22_917) * n_22_916::lseg<s_22_917>@M[LHSCase]
 ]
*/


