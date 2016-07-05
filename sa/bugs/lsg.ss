
data node2{
    node2 n;
    node2 s;
}

HeapPred SLSEG(node2 a,node2 b).

bool lsg(node2 l, node2 e)
infer[SLSEG] requires SLSEG(l,e) ensures true;// res
{
    if (l == e) 
        return true;
    else { 
      if (l==null) return false;
      else return lsg(l.n, e) ;
    }
}
/*

# lsg.ss

OBTAINED :
========

relAssume SLSEG
  SLSEG(l,e)&e!=l & l!=null --> l::node2<n_16_793,s_16_794>@M * 
  HP_5(n_16_793,e) * HP_6(s_16_794,e) .
relAssume SLSEG
  HP_5(n_16_793,e)&true --> SLSEG(n_16_793,e).

Still missing on some base-case equation for pre-pred!

MISSING
=======

relAssume SLSEG
  SLSEG(l,e) & e!=l & l=null --> emp.

relAssume SLSEG
  SLSEG(l,e) & e=l --> emp.

*/

/*

bool lsg(node2 l, node2 e)
infer[SLSEG] requires SLSEG(l,e) ensures true;// res
{
    if (l == e) 
        return true;
    else { 
        return l != null && lsg(l.n, e) ;
    }
}

*/
