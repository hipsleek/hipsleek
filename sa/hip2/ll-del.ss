/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
ll<> == self = null
	or self::node<_, r> * r::ll<> 
	inv true;

HeapPred H(node a).
HeapPred G(node a,node a).

/* function to delete the node after the head in a circular list */
void delete(ref node x)

	requires x::ll<> & x!=null
	ensures x'::ll<> * x::node<_,null>;
	requires x::node<_,null>
	ensures x::node<_,null> & x'=null;
	requires x::node<_,q> & q!=null
	ensures x::node<_,null> & x'=q;
        requires x::node<_,q>
        case {
              q=null -> ensures x::node<_,null> & x'=null;
              q!=null ->  ensures x::node<_,null> & x'=q;
        }
        requires x::node<_,q>
        ensures x::node<_,null> & (q=null & x'=null | q!=null & x'=q);
/*
infer [H,G] 
requires H(x)
ensures G(x,x');
*/
/*
 H(x)&true --> x::node<val_33_789,next_33_790>@M * (HP_791(next_33_790))&true,
 HP_791(next_33_790)&next_33_790=null --> emp&true,
 x::node<val_33_789,next_33_790>@M&next_33_790=null & x'=null --> G(x,x')&
  true,
 (HP_791(next_33_790)) * x::node<val_33_789,v_null_39_808>@M&
  v_null_39_808=null & next_33_790!=null & next_33_790=x' & 
   XPURE(HP_809(next_33_790)) --> G(x,x')&true]


[ H(x_850) ::= x_850::node<val_33_789,next_33_790>@M&next_33_790=null,
 G(x_851,x_852) ::= x_851::node<val_33_789,next_33_790>@M * (HP_854(next_33_790,x_852))&
next_33_790=null,
 HP_854(next_33_790,x_852) ::= 
 emp& XPURE(HP_809(x_852)) & x_852!=null
 or emp&x_852=null
 ]

*/

{
	node tmp;
        dprint;
	if (x.next == null) {
		x = null;
        }
	else
	{
		tmp = x.next;
		x.next=null;
		x = tmp;
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


