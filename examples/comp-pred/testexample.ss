ho_pred ll<n> == true ;


/*
avl_shape[t,b]<a:t>[Base,Rec,Inv] == Base(a,self)
  or self::node[b]<v,n,l,r> *l::avl_shape[t,b](al)*r::avl_shape[t,b](ar)* Rec(a,al,ar,v,n,l,r)
  inv Inv(a)
*/
