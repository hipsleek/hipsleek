data node{
//        int val;
        node prev;
        node next;
}


ll<> == self = null  or self::node< _ , q> * q::ll<>;
dll<p> == self = null or self::node< p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node@NI b).
// seems critical to have @NI
HeapPred G1(node a, node b).

void paper_fix (node x, node p)
//  infer[H1,G1] requires H1(x,p) ensures G1(x,p);
  requires c::ll<> ensures c::dll<p>;
{
        if (x!=null) 
        {
            x.prev=p;
	        paper_fix(x.next,x); 
        }
}

/*

# sll-dll.ss

--sa-dis-split not working

We derive relAssume

[ H1(c,p@NI)&c!=null --> c::node<val_21_807,prev_21_808,next_21_809>@M * 
  HP_810(prev_21_808,p@NI) * HP_811(next_21_809,p@NI),
 HP_811(next_21_809,p@NI) --> H1(next_21_809,c'@NI),
 c::node<val_21_807,p,next_21_809>@M * G1(next_21_809,c) --> G1(c,p),
 emp&c=null --> G1(c,p),
 H1(c,p@NI)&c=null --> emp]

which included a base-case split where

 H1(c,p@NI)&c=null --> G1(c,p)

is splited into:

 emp&c=null --> G1(c,p),
 H1(c,p@NI)&c=null --> emp

Both --sa-en-split & --sa-dis-split produced the same
result. Could we make -dis-split work?

  ("--sa-en-split", Arg.Set Globals.sa_s_split_base, "enable base case splitting of relational assumption");
  ("--sa-dis-split", Arg.Clear Globals.sa_s_split_base, "disable base case splitting of relational assumption");

==========

We derive:

 H1(c,p@NI)&c!=null --> c::node<val_21_807,prev_21_808,next_21_809>@M * 
      HP_810(prev_21_808,p@NI) * HP_811(next_21_809,p@NI)&true,
 
 HP_811(next_21_809,p@NI)&true --> H1(next_21_809,c'@NI)&true,

 c::node<val_21_807,p,next_21_809>@M * G1(next_21_809,c)&true --> G1(c,p)&
  true,

 H1(c,p@NI)&c=null --> G1(c,p)&true

The 4th RelAssume is a target for base-case split since
we have a c=null which contradicts with 1st RelAssume.

Hence:
 H1(c,p@NI)&c=null --> emp
 c=null & emp --> G1(c,p)&true

=========================================================


HP_810 should be dangling as it was instantiated from a field
but never accessed.

Can we avoid @NI annotation for H1?

[ H1(c_847,p_848) ::= 
 emp&c_847=null
 or H1(next_20_828,c') * c_847::node<val_20_826,prev_20_827,next_20_828>@M * 
    HP_810(prev_20_827,p_848)&true
 ,
 G1(c_852,p_853) ::= 
 emp&c_852=null
 or c_852::node<val_20_807,p_853,next_20_809>@M * G1(next_20_809,c_852)&true
 ,
 HP_810(prev_20_808,p) ::=NONE]


====================
without @NI; ERROR in H1

[ H1(c_850,p_851) ::= emp&c_850=null,
 G1(c_852,p_853) ::= 
 emp&c_852=null
 or c_852::node<val_20_807,p_853,next_20_809>@M * G1(next_20_809,c_852)&true
 ,
 HP_810(prev_20_808,p) ::=NONE]



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
