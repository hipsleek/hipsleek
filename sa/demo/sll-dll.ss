data node{
	int val;
	node prev;
	node next;
}


ll<> == self = null  or self::node<_, _ , q> * q::ll<>;
dll<p> == self = null or self::node<_, p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node paper_fix (node c, node p)
  //requires c::ll<> ensures  c::dll<p>;

  infer[H1,G1] requires H1(c,p)  ensures G1(c,p);
{
	if (c!=null) 
	{
		c.prev=p;
                //dprint;
        node d = c.next;
        //dprint;
	paper_fix(d,c);	
	}
	return c;
}
/*
[ 

 H1(c,p)&c!=null --> c::node<val_19_809,prev_19_810,next_19_811>@M * 
  (HP_812(prev_19_810,p)) * (HP_813(next_19_811,p))&true,
 (HP_812(prev_19_810,p)) * (HP_813(next_19_811,p)) * 
  c'::node<val_19_809,p,next_19_811>@M&true --> H1(next_19_811,c')&true,
 G1(next_19_811,c)&c!=null --> G1(c,p_826)&true,
 H1(c,p)&c=null --> G1(c,p)&true]

==========================

[ H1(c_869,p_870) ::= 
 emp&c_869=null
 or c_869::node<val_19_809,prev_19_810,next_19_811>@M&
     XPURE(HP_812(prev_19_810,p_870)) &  XPURE(HP_813(next_19_811,p_870))
 ,
 G1(c_873,p_872) ::= G1(next_19_811,c_871)&c_871!=null]

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
