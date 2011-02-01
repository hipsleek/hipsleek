
ho_pred avl_shape[t,b]<a:t>[Base,Rec,Inv] == Base(a,self)
  or self::node[b]<v,n,l,r> *l::avl_shape[t,b](al)*r::avl_shape[t,b](ar)* Rec(a,al,ar,v,n,l,r)
inv Inv(a)

/*
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
*/
 
