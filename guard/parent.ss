// simpler tll working example

data node{
	node parent;
	node next;
}


// initializes the linked list fields

  HeapPred H(node a, node@NI p).
  HeapPred G(node a, node@NI p).

void set_right (node p, node x)
  infer [H,G] 
  requires H(x,p) 
  ensures G(x,p) ;
  //requires x::tree<p> ensures x::tll<p,res,t>;
{
  node pp = x.parent;
  dprint;
  assert pp'=p assume pp'=p;
}

/*
# parent.ss (see parent-2.slk)

How come rel ass from ASSERT not present here?

[ // BIND
(0)H(x,p@NI) --> x::node<parent_20_900,next_20_901>@M * 
HP_902(parent_20_900,p@NI) * 
HP_903(next_20_901,p@NI),
 // POST
(0)HP_902(parent_20_900,p@NI) * HP_903(next_20_901,p@NI) * 
x::node<p,next_20_901>@M&
p=parent_20_900 --> G(x,p@NI)]

*/
