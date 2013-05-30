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
      c.next = null;

      dprint;
      return t;
}

/*

@12! >>>>>> bind type-checker <<<<<<
@12! node:c
@12! fields:[val_15_763,next_15_764]
@12! node ann:@M
@12! fields ann:[@A,@M]
@12! read-only:false
@12!bind2b3.ss:15: 6: bind: unfolded context:
 List of Failesc Context: [FEC(0, 0, 1  )]


*/
