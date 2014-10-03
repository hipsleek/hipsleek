/* binary search trees */

data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for binary search trees */
bst <sm, lg> == self = null & sm =\inf & lg=-\inf	
	or self::node2<v,p,q> & p = null & q = null & sm = lg & -\inf < sm < \inf
	or self::node2<v, p, q> * p::bst<sm1, lg1> * q::bst<sm2, lg2> 
  & lg1<=v & v<=sm2 & sm=min(sm1,v) & lg=max(lg2,v) & -\inf < v < \inf
  //inv true;
  inv self=null & sm = \inf & lg = -\inf
  | self!=null & sm = lg & -\inf < sm < \inf
  | self!=null & sm <= lg & sm > -\inf & lg < \inf ; // OK for insert..
  //inv self=null & sm=\inf & lg=-\inf | self!=null & sm<=lg; // why fail for insert?

/*
Why Omega time-out for z3? under --dis-imm?

Total verification time: 31.993998 second(s)
	Time spent in main process: 6.25639 second(s)
	Time spent in child processes: 25.737608 second(s)
	Z3 Prover Time: 0.12001 second(s)
 maybe_raise_and_catch_timeout : UNEXPECTED Timeout after 10. secs maybe_raise_and_catch_timeout : UNEXPECTED Timeout after 10. secsloris@loris-desktop:/home2/lo
 */
/* insert a node in a bst */
node2 insert(node2 x, int a)
	requires x::bst<sm, lg> 
	case {
		x = null -> ensures res::node2<a,null,null>; 
		x != null -> ensures res::bst<mi, ma> & mi = min(sm, a) & ma = max(lg, a);
	}
	//ensures res::bst<mi, ma> & mi = min(sm, a) & ma = max(lg, a);
{
	node2 tmp;
    node2 tmp_null = null;

	if (x == null)
		return new node2(a, null, null);
	else
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
		}
		else
		{ 
			//tmp = x.right;
			x.right = insert(x.right, a);
		}

		return x;
	} 
}

