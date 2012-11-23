data node [b] {
	b val;
	node[b] next;
}
ho_pred ll_shape[t,b]<a:t>[Base,Rec,Inv]== Base(a,self)
  or self::node[b]<v,q>* q::ll_shape[t,b]<aq> * Rec(a,aq,v,self,q)
  inv Inv(a);

ho_pred ll_size[int,b]<n:int>[Base,Rec,Inv] refines ll_shape[int,b]<n>
  with {
    Base(n,self) = n=0
    Rec(n,nq,v,self,q) = n=n+1
    Inv(n,self) = n>=0}
  
ho_pred lseg[node[b],b]<p:node[b]> extends ll_shape[node[b],b]<p>
  with
    { Base (p,self) = self=p 
      Rec (p,pq,v,self,q) = pq=p }
    
ho_pred ll_tail[node[b],b]<tx:node[b]> refines lseg[node[b],b]<tx>
  with
    { Base(tx,self) = self::node[b]<_, null> 
      Rec(tx,txq,v,self,q) = q!=null  }
     
ho_pred ll_tail_size[int,b]<n>[Base,Rec,Inv] refines ll_size[int,b]<n>
  with { Base(n,self) = n=1 
         Inv(n,self) = n>=1}
     
ll_tail2<tx,n> == finalizes ll_tail[int]<tx> split ll_tail_size[int]<n>;
	
lseg2<p,n> == finalizes lseg[int]<p> split ll_size[int]<n>;
  
/*
ll_tail<tx> == self::node<_, null> & tx=self
	or self::node<_, r> * r::ll_tail<tx> & r!=null;

lseg<p> == self=p
	or self::node<_, r> * r::lseg<p>;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
	inv n>=1;

	
lseg2<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg2<p, n-1>
	inv n>=0;
*/
lemma "lseg2" self::lseg2<p, n> <-> self::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;
lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;
//lemma "ll_tail2_1" self::ll_tail2<t, n> <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;


//lemma "composite" self::lseg2<y, n> * y::lseg2<ty, m-1> * ty::node<_, null> <-> self::ll_tail2<ty, m+n>;
//lemma self::lseg2<p, n> -> self::lseg2<q, n-1> * q::node<_, p>;
//lemma "lsegbreakmerge" self::lseg<p> <-> self::lseg<q> * q::lseg<p>;
//lemma "lltail2lseg" self::ll_tail<t> <-> self::lseg<t> * t::node<_, null>;
//lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;

void append(node x, node tx, node y, node ty)
//	requires x::ll_tail<tx> * y::ll_tail<ty>
//	ensures x::ll_tail<ty>;
	requires x::ll_tail2<tx, n> * y::ll_tail2<ty, m>
	ensures x::ll_tail2<ty, m+n>;
	//ensures x::lseg2<q,a> * q::lseg2<ty,b> * ty::node<_,null> & a+b+1=m+n;
	//ensures x::lseg2<ty, m+n-1> * ty::node<_, null>;
{
	tx.next = y;
}
/*
****************************************************************************************************************************
 lemma "ll_tail2" self::ll_tail2<t, n>
   <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;

This is a composite of lseg and ll_tail2 lemma. A hand-trace
looks like below. Please chekc if it works!

===============
x::ll_tail2<tx, n> * y::ll_tail2<ty, m> |- tx:node(_,_)

x::lseg2<tx, n-1> * tx:node<_,null> * y::ll_tail2<ty, m>

  {tx.nexy = y }

x::lseg2<tx, n-1> * tx:node<_,y> * y::ll_tail2<ty, m>
    |- x::ll_tail2<ty, m+n>

x::lseg2<tx, n-1> * tx:node<_,y> * y::ll_tail2<ty, m>
    |- x::lseg2<q,a> * q::lseg2<ty,b> * ty::node<_,null>
              & a+b+1=m+n

tx:node<_,y> * y::ll_tail2<ty, m>
    |- tx::lseg2<ty,b> * ty::node<_,null>
              & n-1+b+1=m+n

tx:node<_,y> * y::ll_tail2<ty, m>
    |- tx::node(_,q)*q::lseg2<ty,b-1> * ty::node<_,null>
              & n-1+b+1=m+n

y::ll_tail2<ty, m>
    |- y::lseg<ty,b-1> * ty::node<_,null>
              & n-1+b+1=m+n

y::lseg2<ty, m-1> * ty::node<_, null> 
	|- y::lseg<ty,b-1> * ty::node<_,null>
              & n-1+b+1=m+n	

ty::node<_, null>		
	|- ty::node<_,null>
              & n-1+b+1=b+n	
		  
*/
