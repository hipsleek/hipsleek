
data node2{
    node2 n;
    node2 s;
}

HeapPred SLSEG(node2 a,node2 b).

bool lsg(node2 l, node2 e)
infer[SLSEG] requires SLSEG(l,e) ensures true;// res
{
    if (l == e) return true;
    else return l != null && lsg(l.n, e) ;
}

