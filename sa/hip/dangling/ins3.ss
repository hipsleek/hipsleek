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

##ins2.ss
[ H(x)&x!=null --> x::node<val_34_512',next_34_513'>@M * HP_541(next_34_513')
  true,
 HP_541(v_node_34_514')&true --> H(v_node_34_514')&true,
 H(x)&x=null --> emp&true,

 res::node<v,x>@M&x=null --> G(x,res)&true,

 H(x) * res::node<v,x>@M&x!=null --> G(x,res)&true,

 G(v_node_34_554,v_node_34_558) * x::node<val_34_548,v_node_34_558>@M&
  res=x --> G(x,res)&true]

##ins3.ss
[ H(x)&x!=null --> x::node<val_29_512',next_29_513'>@M * HP_538(next_29_513')
  true,
 HP_538(t_19')&true --> H(t_19')&true,
 H(x)&x=null --> emp&true,
 res::node<v,x>@M&x=null --> G(x,res)&true,

 HP_538(t_555) * x::node<val_29_541,t_555>@M * res::node<v,x>@M&
  true --> G(x,res)&true,

 G(next_35_552,v_node_35_557) * x::node<val_29_541,v_node_35_557>@M&
  res=x --> G(x,res)&true]


Your current implementation obtained:

[ G(x_563,res_564) ::= res_564::node<v,x_565>@M * HP_566(x_565,x_563)&true,
 H(x_575) ::= 
 x_575::node<val_29_560,next_29_513'>@M * H(next_29_513')&true
 or emp&x_575=null
 ,
 HP_566(x_565,x_573) ::= 
 x_565::node<val_29_512',next_29_561>@M * HP_566(x_569,next_29_561)&true
 or x_565::node<v,x_571>@M * HP_566(x_571,next_35_552)&true
 or emp&x_565=null
 ]

PROBLEM : H seems a bit aggressive. A dangling predicate seems
to have been unfolded by HP(n) := n=null. Please remember that
this is different from HP(n) & n=null --> emp.

For H, I was expecting:
 H(x_568) ::= 
 x_568::node<val_28_560,next_28_513'>@M * H(next_28_513')&true
 x_568::node<val_28_560,next_28_513'>@M * HP(next_28_513')
 or emp&x_568=null

For G, I was expecting:
 G(x_563,res_564) ::= res_564::node<v,x_565>@M * H6(x_565,x_563)&true,
 H6(x_565,x_573) ::= 
 x_568::node<val_28_560,next_28_513'>@M * H6(next_28_513',_)&true
 x_568::node<val_28_560,next_28_513'>@M * HP(next_28_513')
 or emp&x_565=null


*/
