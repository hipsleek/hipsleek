data node{
	int val;
	node next;
}


node paper_fix (node c)
  requires c::node<_,p>
  ensures res=p;
{
      node t;
      t = 
        bind c to (vv,nn) 
        in 
        nn;
      dprint;
      return t;
}

/*

Added bind expression whose RHS is an expression ...

Why is there a parsing error for bind in the RHS of assignment?

File "bind2b2.ss", line 15, characters 8-9
 --error: Stream.Error("[expression] expected after EQ (in [assignment_expression])")


*/
