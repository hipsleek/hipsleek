data node2{
	node2 n;
	node2 s;
}

//skipll<> == self=null 	or	self::node2<p,q> * q::skipll<> * p::lseg<q>;

lseg<q> ==  self=q 	
   or	self::node2<n,null>* n::lseg<q>
inv true;
	
HeapPred SLL(node2 a).
HeapPred SLSEG(node2 a,node2@NI b).
HeapPred SLSEGP(node2 a,node2@NI b).
PostPred G(node2 a,node2@NI b).

bool skip0(node2 l, node2 e) 
//  infer[SLSEG,G] requires SLSEG(l,e) ensures G(l,e) & res;// res
requires l::lseg<e> ensures l::lseg<e> & res;
{
	if (l == e) return true;
	else if (l==null) return false;
	else  {
          if (l.s==null) return skip0(l.n, e);
          else return false;
        }
}

/*
# skip0.ss

  infer[SLSEG,G] requires SLSEG(l,e) ensures G(l,e) & res;// res

WORKS
=====

[

SLSEG(l_840,e_841) ::= 
 SLSEG(n_24_834,e_841) * l_840::node2<n_24_834,s_24_835>@M&s_24_835=null & 
 e_841!=l_840
 or emp&e_841=l_840
 ,

G(l_844,e_845) ::= 
 emp&e_845=l_844
 or l_844::node2<n_24_815,s_24_816>@M * G(n_24_815,e_845)&e_845!=l_844 & 
    s_24_816=null
 ]

*/
