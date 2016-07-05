/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
/*
ll<> == self = null
	or self::node<_, r> * r::ll<> 
	inv true;
*/

HeapPred H(node a).
HeapPred G(node a,node a).

/* function to delete the node after the head in a circular list */
void delete(ref node x)
/*
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
*/
infer [H,x,G] 
requires H(x)
ensures G(x,x');

/*
Got:

[ H(x_835) ::= x_835::node<val_61_789,next_61_790>@M&next_61_790=null,
 G(x_836,x_837) ::= x_836::node<val_61_789,next_61_790>@M * (HP_839(next_61_790,x_837))&
next_61_790=null,
 HP_839(next_61_790,x_837) ::= 
 emp&x_837=null
 or emp&x_837!=null
 ]

but expecting:
        requires x::node<_,q>
        ensures x::node<_,null> & (q=null & x'=null | q!=null & x'=q);

*/

{
	node tmp;
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
For hip ll-del.ss, I got:

  H(x)&true --> x::node<val_57_793,next_57_794>@M * (HP_795(next_57_794))&true,
 (HP_795(next_57_794)) * x::node<val_57_793,next_57_794>@M&
  next_57_794=null & x'=null --> G(x,x')&true,
 (HP_795(x')) * x::node<val_57_793,v_null_63_813>@M&x'!=null & 
  v_null_63_813=null --> G(x,x')&true]
*************************************


From sleek, proof log I got:

 id: 19; caller: []; line: 64; classic: false; kind: POST; hec_num: 5; evars: []; c_heap: emp
 checkentail (HP_795(next_57_794)) * x_810::node<val_57_793,v_null_63_813>@M[Orig]&
x=x_810 & next_57_794!=null & !(v_bool_57_770') & next_57_794!=null & 
!(v_bool_57_770') & v_null_63_813=null & next_57_794=next_63_809 & 
next_57_794=x'&{FLOW,(22,23)=__norm}[]
 |-  G(x,x')&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ (HP_795(x')) * x::node<val_57_793,v_null_63_813>@M&
   XPURE(HP_815(next_57_794)) & x'!=null & v_null_63_813=null --> G(x,x')&
  true]
res:  [
  HP_795(next_57_794)&x=x_810 & next_57_794!=null & !(v_bool_57_770') & next_57_794!=null & !(v_bool_57_770') & v_null_63_813=null & next_57_794=next_63_809 & next_57_794=x'&{FLOW,(22,23)=__norm}[]
  es_infer_vars/rel: [x]
  ]

This problem seem to have been triggered by some side-effects,
as when I cut it out for sleek (ll-del2.slk); I got the correct answer:

 <1>emp&x=x_810 & next_57_794!=null & !(v_bool_57_770') & next_57_794!=null & !(v_bool_57_770') & v_null_63_813=null & next_57_794=next_63_809 & next_57_794=x' & x=x_810 & next_57_794=x'&{FLOW,(19,20)=__norm}[]
 inferred hprel: [(HP_6(next_57_794)) * 
                   x_810::node<val_57_793,v_null_63_813>@M&
                   next_57_794!=null & 
                   v_null_63_813=null --> G(x_810,next_57_794)&true]

There seems a problem with es_history!
       es_history: [x::node<val_57_793,next_57_794>@M[Orig]]

*/



