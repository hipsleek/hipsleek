
data node2{
    node2 n;
    node2 s;
}

HeapPred SLSEG(node2 a,node2 b).
HeapPred G(node2 a,node2 b).

lseg<e> == 
 emp&e=self & !(e!=self & self!=null)
  or self::node2<n,_>@M& n::lseg<e> & 
      e!=self
     inv true;

bool lsg(node2 l, node2 e)
/*
  infer[SLSEG,G] 
  requires SLSEG(l,e) 
  ensures G(l,e);// res
*/
  requires l::lseg<e>
  ensures true;
{
    if (l == e) 
        return true;
    else { 
        return l != null && lsg(l.n, e) ;
    }
}

/*

# lsgB.ss

strict && caused some problems..

lhs_contra seems too strong?

[ SLSEG(l,e)&true --> emp&((e+1)>l | l!=null) & (l!=null | l>(e-1)),
 SLSEG(l,e)&e!=l & l!=null --> l::node2<n_19_795,s_19_796>@M * 
  (HP_797(n_19_795,e)) * (HP_798(s_19_796,e))&true,
 HP_797(n_19_795,e)&true --> SLSEG(n_19_795,e)&true,
 SLSEG(l,e)&e=l --> G(l,e)&true,
 (HP_798(s_19_796,e)) * l::node2<n_19_795,s_19_796>@M * (G(n_19_795,e))&
  e!=l --> G(l,e)&true,
 (HP_798(s_19_796,e)) * l::node2<n_19_795,s_19_796>@M * (G(n_19_795,e))&
  e!=l --> G(l,e)&true]

========

# lsgB.ss

[ SLSEG(l_849,e_850) ::= 
 emp&e_850=l_849 & !((e_850!=l_849 & l_849!=null))
 or l_849::node2<n_19_795,s_19_796>@M& XPURE(HP_797(n_19_795,e_850)) & 
     XPURE(HP_798(s_19_796,e_850)) & e_850!=l_849
 ,
 G(l_851,e_852) ::= 
 emp&e_852=l_851
 or l_851::node2<n_19_795,s_19_796>@M * (G(n_19_795,e_852))&
     XPURE(HP_798(s_19_796,e_852)) & e_852!=l_851
 ]




*/
