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
    // H(x)
    if (x==null)
         // H(x) & x=null * res::node(v,x) --> G(x,res)
         //H(x)&x=null --> emp&true,
         //res::node<v,x>@M&x=null --> G(x,res)&true,
		return new node(v, x);
	else
	{
       node t = x.next;
       // H(x) & x!=null * res::node(v,x) --> G(x,res)
       // H(x) * res::node<v,x>@M&x!=null --> G(x,res)&true,
       if (rand()) return new node(v,x);
       else
		{
			x.next = insert(t, v);
            return x;
		}
	}
}

/*

[ H(x)&x!=null --> x::node<val_29_512',next_29_513'>@M * HP_538(next_29_513')&
  true,
 HP_538(t_19')&true --> H(t_19')&true,
 H(x)&x=null --> emp&true,
 res::node<v,x>@M&x=null --> G(x,res)&true,
 HP_538(t_555) * x::node<val_29_541,t_555>@M * res::node<v,x>@M&
  true --> G(x,res)&true,
 G(next_35_552,v_node_35_557) * x::node<val_29_541,v_node_35_557>@M&
  res

[ G(x_563,res_564) ::= res_564::node<v,x_563>@M * HP_565(x_563,res_564)&true,
 H(x_568) ::= 
 x_568::node<val_29_560,next_29_513'>@M * H(next_29_513')&true
 or emp&x_568=null
 ,
 HP_565(x_566,res_564) ::= 
 HP_565(next_29_561,res_564)&true
 or HP_565(next_35_552,v_node_35_557) * 
    res_564::node<val_29_541,v_node_35_557>@M&true
 ]

PROBLEM : H seems a bit aggressive; while HP_565 has a LOOP

For H, I was expecting:
 H(x_568) ::= 
 x_568::node<val_28_560,next_28_513'>@M * H(next_28_513')&true
 x_568::node<val_28_560,next_28_513'>@M * HP(next_28_513')
 or emp&x_568=null


*/
