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
  x.prev.next = x.next;
  x.next.prev = x.prev;
  free(x);
}

/*
--classic


 id: 22; caller: []; line: 16; classic: true; kind: POST; hec_num: 5; evars: []; infer_vars: [H,G,HP_798,HP_799,HP_808,HP_809,HP_822,HP_823]; c_heap: emp
 checkentail HP_808(prev_28_806) * HP_809(next_28_807) * 
prev_28_796::node<prev_28_806,next_28_797>@M[Orig] * HP_822(prev_29_820) * 
HP_823(next_29_821) * next_28_797::node<prev_28_796,next_29_821>@M[Orig]&
next_28_807=next_28_810 & prev_29_820=prev_29_824 & Anon_11=prev_28_796 & 
Anon_12=next_28_797 & x!=null&{FLOW,(22,23)=__norm}[]
 |-  G(x)&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ emp&x!=null --> G(x),
 HP_808(prev_28_806) --> emp,
 HP_809(next_28_807) --> emp,
 HP_822(prev_29_820) --> emp,
 HP_823(next_29_821) --> emp,
 emp&x!=null --> G(x),
 HP_808(prev_28_806) --> emp,
 HP_809(next_28_807) --> emp,
 HP_822(prev_29_820) --> emp,
 HP_823(next_29_821) --> emp]


==========================


 H(x) --> x::node<prev_28_796,next_28_797>@M * HP_798(prev_28_796) * 
  HP_799(next_28_797),
 HP_798(prev_28_796) --> prev_28_796::node<prev_28_806,next_28_807>@M * 
  HP_808(prev_28_806) * HP_809(next_28_807),
 HP_799(next_28_797) --> next_28_797::node<prev_29_820,next_29_821>@M * 
  HP_822(prev_29_820) * HP_823(next_29_821),
 emp&x!=null --> G(x)]

====

[ H(x_831) ::= x_831::node<prev_28_796,next_28_797>@M * 
prev_28_796::node<prev_28_827,next_28_828>@M * HP_808(prev_28_827) * 
HP_809(next_28_828) * next_28_797::node<prev_29_829,next_29_830>@M * 
HP_822(prev_29_829) * HP_823(next_29_830),
 G(x_834) ::= emp&x_834!=null,
 HP_808(prev_28_806) ::= NONE,
 HP_809(next_28_807) ::= NONE,
 HP_822(prev_29_820) ::= NONE,
 HP_823(next_29_821) ::= NONE]


*/
