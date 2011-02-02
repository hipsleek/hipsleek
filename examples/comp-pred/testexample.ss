
/* ho_pred avl_shape[t,b]<a:t>[Base,Rec,Inv] == Base(a,self)
  or self::node[b]<v,n,l,r> * l::avl_shape[t,b]<al> * r::avl_shape[t,b]<ar> * Rec(a,al,ar,v,n,l,r)
  inv Inv(a); 

ho_pred avl_B[t,b]<a:t>[Base,Rec,Inv] refines avl_shape[t,b]<a> 
with 
{ Base(a,self) = self = null }




ho_pred avl_n[int,b]<n:int>[Base,Rec,Inv] extends avl_shape[int,b]<n>
with 
   { Base(n,self) = n = 0 
     Rec(n,nl,nr,v,_,l,r) = n = 1+nl+nr
     Inv(n,self) = n >= 0
   }
 


ho_pred tree_H [int,b]<n:int>[Base,Rec,Inv] extends tree_B[int,b]<n>
 with 
  { 
	Base(n,self) = n= 0
	Rec (n,nl,nr,self,v,l,r) =  nl=n-1 & (nr=n-2 | nr = n-1)
  }
*/

ho_pred avl_S[set[b],b]<S:set[b]>[Base,Rec,Inv] extends avl_shape[set[b],b]<S>  
with
  { Base (S,self) = S={}
    Rec (S,Sl,Sr,v,n,l,r) =  S = union(Sl, Sr, {v}) & forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Sr | y >= v))
  }
