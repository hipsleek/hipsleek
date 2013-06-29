// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b, node c).

node set_right (node x, node r)
//infer [H,G] requires H(x,r) ensures G(x,r,res);
requires x::tree<> ensures x::tll<res,r>;
{
  if (x.right==null) 
  	{
  	  	x.next = r;
  	  	return x;
  	}
  else 
  	{
  		node l_most = set_right(x.right, r);
  		return set_right(x.left, l_most);  		
  	}
}

/*
[ 
  H(x,r)&true --> x::node<left_29_845,right_29_846,next_29_847>@M * 
  HP_8(left_29_845,r) * HP_9(right_29_846,r) * 
  HP_0(next_29_847,r).

  HP_9(right_29_846,r)&right_29_846!=null --> H(right_29_846,r).
 
  HP_8(left_29_845,r)&true --> H(left_29_845,l_47').
 
  HP_9(right_29_846,r)&right_29_846=null --> emp.

 HP_8(left_29_845,r) * x::node<left_29_845,right_29_846,r>@M&res=x & 
  right_29_846=null --> G(x,r,res).

 HP_0(next_29_847,r) * 
  x::node<left_29_845,right_29_846,next_29_847>@M * 
  G(right_29_846,r,l_878) * G(left_29_845,l_878,res)&
  right_29_846!=null --> G(x,r,res).

# tll.ss

PROBLEMS
========
Why  G(left_29_845,l_878,v_node_37_825') still in residue??
--------------
 id: 29; caller: []; line: 37; classic: false; kind: POST; hec_num: 5; evars: []; infer_vars: [H,G,HP_848,HP_849,HP_850]; c_heap: emp
 checkentail HP_850(next_29_847,r) * 
x::node<left_29_845,right_29_846,next_29_847>@M[Orig] * 
G(right_29_846,r,l_878) * G(left_29_845,l_878,v_node_37_825')&
right_29_846!=null & !(v_bool_29_826') & right_29_846!=null & 
!(v_bool_29_826') & right_29_846=right_29_846 & r=r & 
left_29_845=left_29_845 & res=v_node_37_825'&{FLOW,(22,23)=__norm}[]
 |-  G(x,r,res)&true&{FLOW,(22,23)=__norm}[]. 
hprel_ass: [ HP_850(next_29_847,r) * x::node<left_29_845,right_29_846,next_29_847>@M * 
  G(right_29_846,r,l_878) * G(left_29_845,l_878,res)&
  right_29_846!=null --> G(x,r,res)&true]
res:  [
  G(left_29_845,l_878,v_node_37_825')&right_29_846!=null & !(v_bool_29_826') & right_29_846!=null & !(v_bool_29_826') & right_29_846=right_29_846 & r=r & left_29_845=left_29_845 & res=v_node_37_825'&{FLOW,(22,23)=__norm}[]
  ]

*/