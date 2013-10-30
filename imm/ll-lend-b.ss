data node{
 int val;
 node next;
}

ll_ann<n,a1,a2> == self=null & n=0 or
  self::node<_@a1,q@a2>*q::ll_ann<n-1,a1,a2>
  inv n>=0;

ll<n> == self=null & n=0 or
  self::node<_,q>*q::ll<n-1>
  inv n>=0;

int length(node p)
/*
  requires p::ll_ann<n,@A,@L>
  ensures p::ll_ann<n,@A,@A> & res=n;
  requires p::ll_ann<n,@A,@L>
  ensures res=n;
*/
/*  requires p::ll_ann<n,@A,@L>
    ensures p::ll_ann<n,@A,@L> & res=n;*/
/*
   requires p::ll_ann<n,@M,@L> 
   ensures p::ll_ann<n,@M,@A> & res=n; */

   requires p::ll_ann<n,@M,@M> 
   ensures p::ll_ann<n,@A,@A> & res=n ; 

/*  requires p::ll<n>
  ensures  p::ll<n> & res=n;*/
// should fail due to @L in post-condition
{
  if (p==null) return 0;
    else return 1+length(p.next);
}


node tl(node p)
/*
  requires p::node<_,_@A>
  ensures p::node<_,_@A>;
 // fail as expected
  requires p::node<_,y@L>
  ensures p::node<_,_@A> & res=y;
  // succeeds
  requires p::ll<n> & n>0
  ensures p::node<_,res> * res::ll<n-1>;
  requires p::ll_ann<n,@M,@M> & n>0
  ensures p::node<_,res> * res::ll_ann<n-1,@M,@M>;
  requires p::ll_ann<n,@A,@M> & n>0
  ensures p::node<_@A,res> * res::ll_ann<n-1,@A,@M>;

*/
  requires p::ll_ann<n,@A,@M> & n>0
  ensures p::node<_@A,res> * res::ll_ann<n-1,@A,@M>;

{
  return p.next;
}
