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
      /* int x = c.val; */
      c.val = 1;
      bind c to (vv,nn) in { t = nn; vv = 0; };
      dprint;
      return t;
}

/*

Why is this bind inferred as @M?
It should be @L

@7! >>>>>> bind type-checker <<<<<<
@7! node:c
@7! fields:[vv_32,nn_33]
@7! node ann:@M
@7! fields ann:[@L,@L]
@7! read-only:false

*/
