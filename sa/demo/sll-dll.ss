data node{
        int val;
        node prev;
        node next;
}


ll<> == self = null  or self::node<_, _ , q> * q::ll<>;
dll<p> == self = null or self::node<_, p , q> * q::dll<self>;   // p stores the prev node

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
GOT
===
[ H1(c,p)&c!=null --> c::node<val_20_807,prev_20_808,next_20_809>@M * 
  (HP_810(prev_20_808,p)) * (HP_811(next_20_809,p))&true,

 HP_811(next_20_809,p)&true --> H1(next_20_809,c')&true,

 (HP_810(prev_20_808,p)) * c::node<val_20_807,p,next_20_809>@M * 
  (G1(next_20_809,c))&true --> G1(c,p)&true,

 H1(c,p)& XPURE(H1(c,p)) & c=null --> G1(c,p)&true]
         ^^^^^^^^^^^^^^^
EXPECT:
=======
 H1(c,p)&c!=null --> c::node<val_21_809,prev_21_810,next_21_811>@M * 
  HP_2(prev_21_810,p) * HP_3(next_21_811,p)&true.
relAssume H1
 HP_3(next_20_809,p)&true --> H1(next_20_809,c')&true.
relAssume G1
 HP_2(prev_20_808,p) * c::node<val_20_807,p,next_20_809>@M * 
  G1(next_20_809,c)&true --> G1(c,p).
relAssume G1
 H1(c,p) & c=null --> G1(c,p).

--en-sleek-logging-txt

 checkentail H1(c,p)&c=null & !(v_bool_18_784') & c=null & !(v_bool_18_784')&
{FLOW,(22,23)=__norm}[]
 |-  G1(c,p)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ H1(c,p)& XPURE(H1(c,p)) & c=null --> G1(c,p)&true]
                      ^^^^^^^^^^^^^^
res:  [
  emp&c=null & !(v_bool_18_784') & c=null & !(v_bool_18_784')&{FLOW,(22,23)=__norm}[]
  ]

This problem seems to be caused in "hip" as I was not
able to reproduce the same bug in sll-dll-bug3.slk.

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
