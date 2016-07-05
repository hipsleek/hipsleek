data node {
  node prev;
  node next;
}

HeapPred H(node a).
PostPred G(node a).

void free(node x)
  requires x::node<_,_>
  ensures emp;

void remove(node x)
  infer [H,G]
  requires H(x)
  ensures G(x);
/*
  requires p::node<pp,pn>*x::node<p,n>*n::node<np,nn>
  ensures  p::node<pp,n>*n::node<p,nn>;
  requires x::node<null,n>*n::node<np,nn>
  ensures  n::node<null,nn>;
  requires p::node<pp,pn>*x::node<p,null>
  ensures  p::node<pp,null>;
  requires x::node<null,null>
  ensures  emp;
*/
{
  if (x.prev!=null) 
    x.prev.next = x.next;
  if (x.next!=null) 
    x.next.prev = x.prev;
  free(x);
}

/*
[ HP_807(next_28_805)&
  next_28_805!=null --> next_28_805::node<prev_31_851,next_31_852>@M * 
  HP_853(prev_31_851) * HP_854(next_31_852),
 emp&x!=null --> G(x),
 HP_806(prev_28_804)&
  prev_28_804!=null --> prev_28_804::node<prev_29_822,next_29_823>@M * 
  HP_824(prev_29_822) * HP_825(next_29_823),
 HP_807(next_28_805)&x!=null & next_28_805=null --> G(x),
 HP_806(prev_28_804)&x!=null & prev_28_804=null --> G(x),
 H(x) --> x::node<prev_28_804,next_28_805>@M * HP_806(prev_28_804) * 
  HP_807(next_28_805),
 HP_806(prev_28_804) * HP_807(next_28_805)&x!=null & prev_28_804=null & 
  next_28_805=null --> G(x)]

*/
