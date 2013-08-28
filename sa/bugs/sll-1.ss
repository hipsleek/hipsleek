data node{
	int val;
	node prev;
	node next;
}


HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node paper_fix (node c, node p)
  infer[H1,G1] requires H1(c,p) ensures G1(c,p);
{
	if (c!=null) 
	{
		c.prev=p;
        dprint;
	}
	return c;
}

/*

 State:EXISTS(val_16_745',next_16_747': (HP_771(prev_16_773,p)) * (HP_772(next_16_747',p)) * 
 c'::node<val_16_745'@A,p'@M,next_16_747'@A>@M[Orig]&c=c' & p=p' 
& c'!=null & v_bool_14_748' & c'!=null & v_bool_14_748'&{FLOW,(22,23)=__norm})[]

 */

