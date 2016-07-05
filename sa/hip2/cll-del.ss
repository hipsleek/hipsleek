/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p> == self = p 
	or self::node<_, r> * r::cll<p> & self != p  
	inv true;

hd<> == self = null 
	or self::node<_, r> * r::cll<self>  
	inv true;

HeapPred H(node a).
HeapPred G(node a,node a).

/* function to delete the node after the head in a circular list */
void delete(ref node x)
/*

	requires x::hd<> & x!=null
	ensures x'::hd<>;
*/
infer [H,G] 
requires H(x)
ensures G(x,x');

{
	node tmp;

	if (x.next == x)
		x = null;
	else
	{
		tmp = x.next.next;
		x.next = tmp;
	}
}

/*

 H(x)&true --> x::node<val_35_804,next_35_805>@M 
     * (HP_806(next_35_805))&true,
 
 HP_806(next)&true -->   // x!=next?
   next::node<val_39_821,next_39_822>@M * 
      (HP_823(next_39_822))&true,

 HP_806(x_814)&x=x_814 --> emp&true, // where is x?


 x_814::node<val_35_804,x_814>@M&x'=null & x=x_814 --> G(x,x')&true,

 (HP_823(next_39_822)) * x'::node<val_35_804,next_39_822>@M&x=x' 
     --> G(x,x') & true]


*/


