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
  x.next.prev = x.prev;
  free(x);
}

/*
[ HP_802(prev_28_800)&
  prev_28_800!=null --> prev_28_800::node<prev_29_818,next_29_819>@M * 
  HP_820(prev_29_818) * HP_821(next_29_819),
 HP_803(next_28_801) --> next_28_801::node<prev_30_835,next_30_836>@M * 
  HP_837(prev_30_835) * HP_838(next_30_836),
 emp&x!=null --> G(x),
 H(x) --> x::node<prev_28_800,next_28_801>@M * HP_802(prev_28_800) * 
  HP_803(next_28_801),
 HP_802(prev_28_800)&x!=null & prev_28_800=null --> G(x)]

====

[ HP_820(prev_29_818) ::= NONE,
 HP_821(next_29_819) ::= NONE,
 HP_837(prev_30_835) ::= NONE,
 HP_838(next_30_836) ::= NONE,
 H(x_853) ::= x_853::node<prev_28_800,next_28_801>@M * 
prev_28_800::node<prev_29_847,next_29_848>@M * HP_820(prev_29_847) * 
HP_821(next_29_848) * next_28_801::node<prev_30_849,next_30_850>@M * 
HP_837(prev_30_849) * HP_838(next_30_850)
   \/  x_853::node<prev_28_800,next_28_801>@M * HP_803(next_28_801)&
prev_28_800=null,
 G(x_854) ::= emp&x_854!=null \/  emp&x_854!=null,
 HP_803(next_28_801) ::= NONE]

*/
