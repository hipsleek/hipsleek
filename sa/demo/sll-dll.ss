data node{
        int val;
        node prev;
        node next;
}


ll<> == self = null  or self::node<_, _ , q> * q::ll<>;
//dll<p> == self = null or self::node<_, p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

void paper_fix (node c, node p)
  infer[H1,G1] requires H1(c,p) ensures G1(c,p);
//  requires c::ll<> ensures c::dll<p>;
{
        if (c!=null) 
        {
            c.prev=p;
	        paper_fix(c.next,c); 
        }
}

//# sll-dll.ss

/*
[ H1(c_871,p_873) ::= 
 emp&c_871=null
 or (H1(next_20_830,c')) * c_871::node<val_20_828,prev_20_829,next_20_830>@M&
     XPURE(HP_810(prev_20_829,p_872))
 ,
 G1(c_874,p_875) ::= 
 emp&c_874=null
 or c_874::node<val_20_807,p_875,next_20_809>@M * (G1(next_20_809,c_874))&
     XPURE(HP_810(prev_20_808,p_875))
 ]

--sa-inlining

[ H1(c_859,p_861) ::= 
 (H1(next_20_818,c')) * c_859::node<val_20_816,UU_HP_798_UU,next_20_818>@M&
 true
 or emp&c_859=null
 ,
 G1(c_862,p_863) ::= 
 c_862::node<val_20_795,p_863,next_20_797>@M * (G1(next_20_797,c_862))&true
 or emp&c_862=null
 ]

--sa-inlining

[ H1(c_871,p_873) ::= 
 (H1(next_20_830,c')) * c_871::node<val_20_828,UU_HP_810_UU,next_20_830>@M&
 true
 or emp&c_871=null
 ,
 G1(c_874,p_875) ::= c_874::dll<p_875>@M[LHSCase]&true]



*/

  /*
void remove (node c)
	
	//verbose:
	//requires c::node<_,p,q>*p::node<v,a,c>*q::dll<c> ensures p::node<v,a,q>*q::dll<p>;	
	//requires c::node<_,null,q>*q::dll<c> ensures q::dll<p>;	
	
	//compact: 
	//requires p::node<v,a,c>*c::dll<p> & c!=null ensures p::dll<a>;	
	//requires c::dll<null> & c!=null ensures q::dll<null>;	
	
	infer [G1] requires p::node<v,a,c>*G1(c,p) & c!=null ensures G1(p,a);
	infer [G1] requires G1(c,null) & c!=null ensures G1(_,null);
	
	
{
	if (c.prev != null) c.prev.next = c.next ;
	if (c.next != null) c.next.prev = c.prev ;
}
  
  
  */
//ll2<n,S> == self = null & n=0 & S={}  or self::node<v, _ , q> * q::ll2<n-1,S1> & S=union(S1,{v});
//dll2<p,n,S> == self = null & n=0 & S={} or self::node<v, p , q> * q::dll2<self,n-1,S1> &  S=union(S1,{v});
/*
node verif_fix (node c, node p)
	requires c::ll<>	ensures c::dll<p>;
//requires c::ll2<n,S> ensures c::dll2<p,n,S> ;
{
	if (c!=null) 
	{
		c.prev=p;
		verif_fix(c.next,c);	
	}
	return c;
}
*/
