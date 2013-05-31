data node{
	int val;
	node prev;
	node next;
}

/*
ll<> == self = null  or self::node<_, _ , q> * q::ll<>;
dll<p> == self = null or self::node<_, p , q> * q::dll<self>;   // p stores the prev node
*/

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node paper_fix (node c, node p)
  infer[H1,G1] requires H1(c,p) ensures G1(c,p);
{
  if (c!=null) 
    {
      bind c to (_,pp,nn) in {
        pp=p;
        dprint;
        paper_fix(nn,c);
      }
    }
  return c;
}

  /*

[

H1(c,p)&c!=null --> c::node<Anon_784,pp_785,nn_786>@M * 
  (HP_787(pp_785,p)) * (HP_788(nn_786,p))&true,
 HP_788(nn_786,p)&c'!=null --> H1(nn_786,c')&true,
 (HP_787(pp_785,p)) * (G1(nn_786,c)) * c::node<Anon_784,p,nn_786>@M&
  true --> G1(c,p)&true,
 H1(c,p)&c=null --> emp&true,
 H1(c,p)&c=null --> G1(c,p)&true]
 ^^^^^^^ to remove
 

 checkentail H1(c,p)&c=null & !(v_bool_18_760') & c=null & !(v_bool_18_760') & c=res&
{FLOW,(22,23)=__norm}[]
 |-  G1(c,p)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ H1(c,p)&c=null --> G1(c,p)&true,
 H1(c,p)&c=null --> emp&true]


H1(c,p)&c!=null --> c::node<Anon_11',pp',nn'>@M * (HP_784(pp',p)) * 
  (HP_785(nn',p))&true,
 (HP_785(nn',p)) * c'::node<Anon_11',p,nn'>@M&true --> H1(nn',c')&true,
 (HP_784(pp_786,p)) * (G1(nn_797,c)) * c::node<Anon_796,p,nn_797>@M&
  true --> G1(c,p)&true,
 H1(c,p)&c=null --> emp&true,
 emp&c=null --> G1(c,p)&true]

 


[ H1(c,p)&c!=null --> c::node<Anon_11',pp',nn'>@M * (HP_784(pp',p)) * 
  (HP_785(nn',p))&true,

 (HP_785(nn',p)) * c'::node<Anon_11',p,nn'>@M&true --> H1(nn',c')&true,
  ^^^^^ wrong ^^^^

 (HP_784(pp_786,p)) * (G1(nn_797,c)) * c::node<Anon_796,p,nn_797>@M&
  true --> G1(c,p)&true,

 H1(c,p)&c=null --> emp&true,

 emp&c=null --> G1(c,p)&true]


[ H1(c,p)&c!=null --> c::node<Anon_11',pp',nn'>@M * (HP_771(pp',p)) * 
  (HP_772(nn',p))&true,
 c'::node<Anon_11',pp_773,nn'>@M * (HP_771(pp_773,p)) * (HP_772(nn',p))&
  true --> H1(nn',c')&true,
 (G1(nn_782,c)) * c::node<Anon_11',p,nn'>@M&true --> G1(c,p)&true,
 H1(c,p)&c=null --> G1(c,p)&true]

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
