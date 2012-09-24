data node {
	int val; 
	node next;
	node parent;
	node left;
	node right;	
}

ll<S> == self = null & S = {}
		or self::node<_@L,n,_@A,_@A,_@A> * n::ll<Sn> & S = union(Sn,{self})
		inv true
		memE S->(node<@L,@M,@A,@A,@A>);

tree<p,S> == self=null & S = {}
		or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tree<self,Sr> & S = union(Sl,Sr,{self})
            & self!=p & p notin Sl & p notin Sr
  inv (self=null & S={} | self!=null & self in S) & p notin S
		memE S->(node<@L,@A,@M,@M,@M>);

// can we compute fixpoint automatically?
// is there a way to complete pure definition from diagram/structure & base cases?
treeseg<p,ph,h,S> == self = h & S = {}  & p=ph // can h be null?
  or self::node<_@L,_@A,p,l,r> * l::treeseg<self,ph,h,Sl> * r::tree<self,Sr> 
      & h != self & h notin Sr & h notin Sl 
  & S = union(Sl,Sr,{self}) & p!=ph & p notin Sr & p notin Sl & self!=p & (ph=self | ph in Sl)
  or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::treeseg<self,ph,h,Sr> & h != self & h notin Sl & h notin Sr
  & S = union(Sl,Sr,{self}) & p!=ph & p notin Sr & p notin Sl & self!=p & (ph=self | ph in Sr)
  inv h notin S & p notin S  
  & (self=h & S={} | self!=h & self in S)  // inv must not contain existential variables!
  & (p=ph & S={} | ph!=p & ph in S)
		memE S->(node<@L,@A,@M,@M,@M>);	

/* tseg<hd,S> == hd = self & S = {} & hd != null */
/* 	or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tseg<hd,Sr> & hd in Sr & S = union({self},Sl,Sr) */
/* 	or self::node<_@L,_@A,p,l,r> * l::tseg<hd,Sl> * r::tree<self,Sr> & hd in Sl & S = union({self},Sl,Sr) */
/* 	inv hd != null */
/* 	memE S->(node<@L,@A,@M,@M,@M>); */
		
// not proven successfully
lemma self::tree<p,S> <- self::treeseg<p,ph,h,S1> * h::tree<ph,S2> & S = union(S1,S2);

/* lemma self::tree<p,S> & h in S */
/*   -> self::treeseg<p,ph,h,S1> * h::node<_@L,_@A,ph,l,r> * l::tree<h,S2> * l::tree<h,S3> & S = union(S1,S2,S3,{h}); */

/* lemma self::tseg<hd,S> -> self::treeseg<_,hd,Ss> * hd::node<_@L,_@A,_@M,_@M,_@M> & S = union(Ss,{hd}); */

