data node {
  node next; 
  node p;
  node l;
  node r;
  int key;
}

ll<n,B> == self=null & n=0 & B={}
	or self::node<t, _,_,_,k> * t::ll<n-1,B1> & B=union({self},B1)
	inv n>=0;

treep<p,B> == self=null & B={}
	or self::node<_,p,l,r,_> * l::treep<self,B1> * r::treep<self,B2> & B=union({self},union(B1,B2));

global node q1s, q1t, q2;

// type error : could not infer for c.

void treeRemove(ref node q) 
  requires q::treep<null, B>  
  ensures q'::treep<null, B1> & B = union(B1, {c}) 
  or q'::treep<null, B>;
