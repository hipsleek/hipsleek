/* bounded lists */

/* representation of a node */
data node [b]{
	b val; 
	node[b] next;	
}

ho_pred ll_shape[t,b]<a:t>[Base,Rec,Inv] == Base(a,self)
  or self::node[b]<v,q> * q::ll_shape<aq> * Rec(a,aq,v,self,q)
  inv Inv(a);

ho_pred ll_B [t,b]<a:t>[Base,Rec,Inv] refines ll_shape[t,b]<a>
  with {Base(a,self) = self = null }
  
ho_pred llS[int,b]<n:int>[Base,Rec,Inv] extends ll_B[int,b]<n>
  with
    {
      Base(n,self) = a=0
      Rec (n,nq,v,self,q) = n=nq+1
    }
       
ho_pred bndl [(b,b),b]<(a1,a2):(b,b)> [Base,Rec,Inv] extends ll_B[(b,b),b]<(a1,a2)>
  with
   {
     Base (a1,a2,self) =a1<=a2
     Rec (a1,a2,aq1,aq2,v,self,q) = a1=aq1 & a2=aq2 & a1<=q<=a2
   }

ll<n> == finalizes ll_B[int]<a> split llS[int]<n>;
bndl<n,sm,bg> == finalizes bndl[int]<sm,bg> split ll_B[int]<n>;



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

