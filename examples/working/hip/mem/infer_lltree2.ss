data node {
	int val; 
	node next;
	node parent;
	node left;
	node right;	
}

ll<S> == self = null //& S = {}
		or self::node<_@L,n,_@A,_@A,_@A> * n::ll<Sn> //& S = union(Sn,{self})
		inv true
		memE S->();
		//memE S->(node<@L,@M,@A,@A,@A>);

tree<p,S> == case {
  S={} -> [] self=null; //& S = {};
  S!={} -> [] self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tree<self,Sr> // & S = union(Sl,Sr,{self})
  & self!=p & p notin Sl & p notin Sr;}
  inv (self=null & S={} | self!=null & self in S) & p notin S
  memE S->();
		//memE S->(node<@L,@A,@M,@M,@M>);

treeseg<p,ph,h,S> == case {
  self = h -> []  p=ph; 
  self!=h -> [] self::node<_@L,_@A,p,l,r> * l::treeseg<self,ph,h,Sl> * r::tree<self,Sr> 
      & h notin Sr & h notin Sl 
  & p!=ph & p notin Sr & p notin Sl & self!=p & (ph=self | ph in Sl)
  or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::treeseg<self,ph,h,Sr>  & h notin Sl & h notin Sr
  & p!=ph & p notin Sr & p notin Sl & self!=p & (ph=self | ph in Sr); }
  inv h notin S & p notin S  
  & (self=h & S={} | self!=h & self in S)  
  & (p=ph & S={} | ph!=p & ph in S)
  memE S->();
       //memE S->(node<@L,@A,@M,@M,@M>);	
		
// proven successfully
lemma self::tree<p,S> <- self::treeseg<p,ph,h,S1> * h::tree<ph,S2> & S = union(S1,S2); 

// proven successfully
lemma self::tree<p,S> & h in S & h=self
   -> self::treeseg<p,ph,h,S1> * h::node<_@L,_@A,ph,l,r>
        * l::tree<h,S2> * r::tree<h,S3> & S = union(S1,S2,S3,{h})
        & h notin S1 & h notin S2 & h notin S3;


node list_remove_first(ref node q1s)
requires q1s::ll<S>
ensures res::node<_@L,q@M,_@A,_@A,_@A> * q::ll<S1> & S = union(S1,{res}) & q1s' = q & q1s = res;

void tree_remove(node x, ref node q1t)
requires q1t::tree<p,S> & x in S
ensures q1t'::treeseg<p,px,x,S1> * px::tree<_,S2> & S = union({x},S1,S2); //'

void list_add_first(ref node q2, node y)
requires q2::ll<S> * y::node<v@L,_@M,_@A,_@A,_@A>
ensures  y::node<v@L,q2@A,_@A,_@A,_@A> * q2::ll<S> & q2' = y;

void tree_add(ref node q1t, node y)
requires q1t::tree<p,S> * y::node<v@L,_@A,_,_,_>
ensures q1t::tree<p,S1> & S1 = union(S,{y});

void totree(ref node q1s, ref node q1t)
requires q1s::ll<S>
ensures q1t::tree<p,S>;

void move_request(ref node q1s, ref node q2, ref node q1t)
requires q2::ll<Sq> * q1s::ll<S> &* q1t::tree<p,S>
ensures q2'::ll<Sq1> * q1s'::ll<Ss> &* q1t'::tree<p,Ss>  & S = union(Ss,{q1s}) & Sq1 = union(Sq,{q1s});//'
{
node c;
c = list_remove_first(q1s);
if (c == null) return;
tree_remove(c,q1t);
list_add_first(q2,c);
}
