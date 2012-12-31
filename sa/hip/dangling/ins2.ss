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
       // H(x) & x!=null * res::node(v,x) --> G(x,res)
       // H(x) * res::node<v,x>@M&x!=null --> G(x,res)&true,
       if (rand()) return new node(v,x);
       else
		{
			x.next = insert(x.next, v);
            return x;
		}
	}
}

/*
[ 
 H(x)&x!=null --> x::node<val_28_512',next_28_513'>@M * HP_541(next_28_513')&
  true,
 HP_541(v_node_28_514')&true --> H(v_node_28_514')&true,

 H(x) * res::node<v,x>@M&x!=null --> G(x,res)&true,
 G(v_node_28_554,v_node_28_558) * x::node<val_28_548,v_node_28_558>@M&
  res=x --> G(x,res)&true]
*************************************


 H(x)&x!=null --> x::node<val_28_512',next_28_513'>@M * HP_541(next_28_513')& true, (A)
 H(x) * res::node<v,x>@M&x!=null --> G(x,res)&true, (B)

 (A) should be used to refine (B), as the LHS can be expanded.



[ G(x_563,res_564) ::= res_564::node<v,x_563>@M * HP_565(x_563,res_564)&true,
 H(x_568) ::= 
 x_568::node<val_28_560,next_28_513'>@M * H(next_28_513')&true
 or emp&x_568=null
 ,
 HP_565(x_566,res_564) ::= 
 HP_565(next_28_561,res_564)&true
 or HP_565(v_node_28_554,v_node_28_558) * 
    res_564::node<val_28_548,v_node_28_558>@M&true
 ]

PROBLEM : H seems a bit aggressive; while HP_565 has a LOOP

For H, I was expecting:
 H(x_568) ::= 
 x_568::node<val_28_560,next_28_513'>@M * H(next_28_513')&true
 x_568::node<val_28_560,next_28_513'>@M * HP(next_28_513')
 or emp&x_568=null

 I think  this may be because you derived:
   HP(n) & n=null --> emp
 which you turned into:
   HP(n) ::= n=null
 that is then inlined. This may be unsound in
 my opinion.


*/
