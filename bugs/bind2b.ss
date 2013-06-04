data node{
	int val;
	node next;
}


HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node paper_fix (node c)
  requires c::node<_,p>
  ensures res=p;
{
      node t;
      t = c.next;
      c.val = 0;
      dprint;
      return t;
}

/*

@7! >>>>>> bind type-checker <<<<<<
@7! node:c
@7! fields:[val_15_762,next_15_763]
@7! node ann:@L
@7! fields ann:[@A,@L]
@7! read-only:true
@7!bind2b.ss:15: 10: bind: unfolded context:
 L

*/
