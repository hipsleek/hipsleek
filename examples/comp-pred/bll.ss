/* bounded lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}
//#include<ll-shape.ss>
ll-shape(a)[Base,Rec,Inv]= Base(a,self)
  or self::node<v,q>* q::ll-shape(aq) & Rec(a,aq,v,self,q)
  inv Inv(a);
llBase (a,self) = self=null 
llsBase(a,self) = a=0 
llsRec(a,aq,v,self,q) = a=aq+1 
ll<n> = ll-shape<> [llsBase,llsRec,llsInv : n] [Base = llBase : ] 
  
bndlBase (a1,a2,self) =a1<=a2
bndlRec (a1,a2,aq1,aq2,v,self,q) = a1=aq1 & a2=aq2 & a1<=q<=a2

bndl<n,sm,bg> = ll<n>[bndlBase,bndlRec:sm,bg]

/* view for bounded lists */
/*bndl<n, sm, bg> == self = null & n = 0 & sm <= bg
	or self::node<d,p> * p::bndl<n-1, sm, bg> & sm <= d & d <= bg  
	inv sm <= bg & n >= 0;
*/
/* insert a node as the first one in a bounded list */
node insert(node x, int v)

	requires x::bndl<n, sm, bg> & sm <= v & v <= bg 
	ensures res::bndl<n+1, sm, bg>;

{
	return new node(v,x);
}

/* delete a node from a bounded list */
node delete(node x)

	requires x::bndl<n,sm,bg> & x != null
	ensures res::bndl<n-1, sm, bg>;

{
	return x.next;
}

