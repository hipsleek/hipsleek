
data node2{
    node2 n;
    node2 s;
}

HeapPred SLSEG(node2 a,node2 b).
HeapPred G(node2 a,node2 b).

bool lsg(node2 l, node2 e)
  infer[SLSEG,G] 
 requires SLSEG(l,e) 
 ensures G(l,e);// res
{
    if (l == e) 
        return true;
    else { 
      if (l==null) return false;
      else return lsg(l.n, e) ;
    }
}
/*

# lsgA.ss

OBTAINED :
========

[ SLSEG(l,e)&e!=l & l!=null --> l::node2<n_19_796,s_19_797>@M * 
  (HP_798(n_19_796,e)) * (HP_799(s_19_797,e))&true,
 HP_798(n_19_796,e)&true --> SLSEG(n_19_796,e)&true,
 SLSEG(l,e)&e=l --> G(l,e)&true,
 SLSEG(l,e)&e!=l & l=null --> G(l,e)&true,
 (HP_799(s_19_797,e)) * l::node2<n_19_796,s_19_797>@M * (G(n_19_796,e))&
  e!=l --> G(l,e)&true]

=======


[ SLSEG(l_876,e_877) ::= 
 emp&e_877=l_876
 or emp&e_877!=l_876 & l_876=null
 or l_876::node2<n_19_796,s_19_797>@M& XPURE(HP_798(n_19_796,e_877)) & 
     XPURE(HP_799(s_19_797,e_877)) & e_877!=l_876
 ,
 G(l_878,e_879) ::= 
 emp&e_879=l_878
 or emp&l_878=null & e_879!=l_878
 or l_878::node2<n_19_796,s_19_797>@M * (G(n_19_796,e_879))&
     XPURE(HP_799(s_19_797,e_879)) & e_879!=l_878
 ]

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
