data node{
	int val;
	node prev;
	node next;
}


HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node paper_fix (node c, node p)
  infer[H1,G1] requires H1(c,p) 
  ensures G1(c,p);
{
	if (c!=null) 
	{
		c.prev=p;
                dprint;
        node d = c.next;
        dprint;
	paper_fix(d,c);	
	}
	return c;
}

/*
*******relational assumption ********
*************************************
[ H1(c,p)&c!=null --> c::node<val_19_765',prev_19_766',next_19_767'>@M * 
  (HP_796(prev_19_766',p)) * (HP_797(next_19_767',p))&true,
 c'::node<val_19_805,p,next_19_806>@M * (HP_796(prev_19_798,p)) * 
  (HP_797(next_19_806,p))&true --> H1(next_19_806,c')&true,
 (G1(next_19_806,c)) * c::node<val_19_765',p,next_19_767'>@M&
  true --> G1(c,p)&true,
 H1(c,p)&c=null --> G1(c,p)&true]
*************************************

*************************************
*******relational definition ********
*************************************
[ H1(c_818,p_819) ::= c_818::node<val_19_765',prev_19_766',next_19_767'>@M * 
(HP_797(next_19_767',p_819))&true,
 G1(c_820,p_821) ::= c_820::node<val_19_765',prev_19_816,next_19_817>@M * 
(HP_797(next_19_817,p_821))&c_820=null]
*************************************

*/
