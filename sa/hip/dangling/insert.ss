/* merge sort */

data node {
	int val; 
	node next; 
}

bool rand()
 requires true
 ensures !res or res;

HeapPred H(node a). 
HeapPred G(node a,node b). 

/* function to insert an element in a sorted list */
node insert(node x, int v)
  infer [H,G]
  requires H(x)
  ensures G(x,res);
{
	node tmp;	

    int r = x.val;
	if (rand())
		return new node(v, x);
	else
	{
		if (x.next != null)
		{
			x.next = insert(x.next, v);
      return x;
		}
		else
    {
			x.next = new node(v,null);
      return x;
    }
	}
}

/*
[ H(x)&true --> x::node<val_23_512',next_23_513'>@M * HP_544(next_23_513')&
  true,
 HP_544(next_23_547)&next_23_547!=null --> H(next_23_547)&true,
 HP_544(next_23_547) * x::node<r_582,next_23_547>@M * res::node<v,x>@M&
  true --> G(x,res)&true,
 G(next_23_547,v_node_30_585) * x::node<r_586,v_node_30_585>@M&res=x & 
  next_23_547!=null --> G(x,res)&true,
 HP_544(next_23_547)&next_23_547=null --> emp&true,
 v_node_35_589::node<v,v_null_35_578>@M * x::node<r_590,v_node_35_589>@M&
  res=x & v_null_35_578=null --> G(x,res)&true]

==========================================================
PROBLEM
=======

HP_544 seems a bit aggressive, as it seems to have lost
some dangling predicate.
HP_600 is problematic seem it has a loop!


[ H(x_597) ::= x_597::node<val_23_512',next_23_513'>@M * HP_544(next_23_513')&true,
 G(x_598,res_599) ::= x_598::node<r_590,v_node_35_589>@M * HP_600(v_node_35_589,res_599)&true,
 HP_600(v_node_35_589,res_599) ::= 
 HP_600(v_node_35_605,v_node_35_589)&res_599=x_598
 or v_node_35_589::node<v,v_null_35_578>@M&res_599=x_598 & v_null_35_578=null
 or res_599::node<v,x_598>@M&v_node_35_589=null
 ,
 HP_544(next_23_607) ::= 
 next_23_607::node<val_23_512',next_23_593>@M * HP_544(next_23_593)&true
 or emp&next_23_607=null
 ]

*/
