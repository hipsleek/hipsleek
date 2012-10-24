data node {
	int val;
	node next
}

HeapPred H1(node a).
HeapPred G1(node a, node b).

/* return the tail of a singly linked list */
/* node get_next(ref node x) */
/*   infer[H,G] */
/*   requires H(x) */
/*   ensures G(x',res);//'n>=1 & n=m+1 */
/* { */
/*   node tmp = x.next; */
/*   x.next = null; */
/*   return tmp; */
/*   //	dprint; */
/* } */

node get_next_next(ref node x)
  infer[H1,G1]
  requires H1(x)
  ensures G1(x',res);//'n>=1 & n=m+1
{
  node tmp = x.next.next;
  x.next.next = null;
  return tmp;
  //	dprint;
}

/*

H(x) = x::node<_,q>
G(x,res) = x::node<_,null> & res=q

*/

/*

-----constrs------
H(x) --> x::node<val_22_535',next_22_536'> * HP_551(next_22_536',x)
HP_551(v_node_24_540',x) * x::node<val_22_560,next_23_539'> --> G(x,v_node_24_540')

//dprint: HP_551(v_node_24_540',x) * x::node<val_22_560,next_23_539'> & next_23_539'=null
//Lost infomation: next_23_539'=null


------defs---------
H(x)::  x::node<val_22_535',next_22_536'> * HP_566(x) or x::node<val_22_535',next_22_536'> * HP_563(x)
HP_565(v_node_24_540')::  HP_564(v_node_24_540')
HP_566(x)::  HP_563(x)
G(x,v_node_24_540')::  HP_563(x) * HP_564(v_node_24_540')
HP_551(v_node_24_540',x)::  HP_565(v_node_24_540') * HP_566(x)

*/
