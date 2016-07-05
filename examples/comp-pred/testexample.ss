/* avl trees */

/* representation of a node in an avl tree */
data node[b] {
  b val;
  int height;
  node[b] left;
  node[b] right;
}

data myint {
  int val;
}

ho_pred avl_shape[t,b]<a:t>[Base,Rec,Inv] == Base(a,self)
  or self::node[b]<v,n,l,r> *l::avl_shape[t,b]<al>*r::avl_shape[t,b]<ar>* Rec(a,al,ar,v,n,l,r)
  inv Inv(a);

ho_pred avl_B[t,b]<a:t>[Base,Rec,Inv] refines avl_shape[t,b]<a> with { Base(a,self) = self=null}
 
ho_pred avl_n[int,b]<n:int>[Base,Rec,Inv] extends avl_shape[int,b]<n>
with 
   { Base(n,self) = n = 0 
     Rec(n,nl,nr,v,_,l,r) = n = 1+nl+nr
     Inv(n,self) = n>=0
   }

ho_pred avl_h[int,b]<h:int>[Base,Rec,Inv] extends avl_shape[int,b]<h>
with 
   { Base(h,self) = h = 0 
     Rec(h,hl,hr,v,nh,l,r) = nh=h & -1<=hl-hr<=1  & h=1+max(hl,hr)
     Inv(h,self) = h>=0
   }

ho_pred avl_S[set[b],b]<S:set[b]>[Base,Rec,Inv] extends avl_shape[set[b],b]<S>  
with
  { Base (S,self) = S={}
    Rec (S,Sl,Sr,v,n,l,r) =  S = union(Sl, Sr, {v}) & forall (x : (x notin Sl | x <= v)) & forall (y : (y notin Sr | y >= v))
  }
  
avl<m,n,S> == finalizes avl_S[int]<S>; 


