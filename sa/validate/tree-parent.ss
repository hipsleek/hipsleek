// simpler tll working example

data node{
	node parent;
	node left;
	node right;
}


tree<p> == self::node<p,null,null>
        or self::node<p,l,r> * l::tree<self> * r::tree<self>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node@NI p, node a).
HeapPred G(node@NI p, node a).

void trav (node p, node x)
  infer [H,G] requires H(p,x) ensures G(p,x);
//requires x::tree<pp> & pp=p ensures x::tree<p>;
{
  node tmp = x.parent;
  assume tmp'=p;//'
  if (x.right!=null) 
  	{
//		assert xl'=null;
          trav(x,x.right);
  	}
  else if (x.left!=null) {
          trav(x,x.left);
  }
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup


[ // BIND
(0)H(p@NI,x) --> x::node<parent_24_943,left_24_944,right_24_945>@M * 
HP_946(parent_24_943,p@NI) * HP_947(left_24_944,p@NI) * 
HP_948(right_24_945,p@NI),
 // PRE_REC
(1;0)HP_948(right_24_945,p@NI)&right_24_945!=null & 
p=parent_24_943 |#| x::node<p,left_24_944,right_24_945>@M --> H(x@NI,right_24_945),
 // PRE_REC
(1;2;0)HP_947(left_24_944,p@NI)&left_24_944!=null & 
p=parent_24_943 |#| x::node<p,left_24_944,right_24_945>@M --> H(x@NI,left_24_944),
 // POST
(1;0)HP_946(parent_24_943,p@NI) * HP_947(left_24_944,p@NI) * 
x::node<p,left_24_944,right_24_945>@M * G(x@NI,right_24_945)&
right_24_945!=null & 
p=parent_24_943 --> G(p@NI,x),
 // POST
(1;2;0)HP_946(parent_24_943,p@NI) * HP_948(right_24_945,p@NI) * 
x::node<p,left_24_944,right_24_945>@M * G(x@NI,left_24_944)&
right_24_945=null & left_24_944!=null & 
p=parent_24_943 --> G(p@NI,x),
 // POST
(2;2;0)HP_946(parent_24_943,p@NI) * HP_947(left_24_944,p@NI) * 
HP_948(right_24_945,p@NI) * x::node<p,left_24_944,right_24_945>@M&
right_24_945=null & left_24_944=null & 
p=parent_24_943 --> G(p@NI,x)]


[ G(p_1018,x_1019) ::=(1;2;0) HP_946(parent_24_943,p_1018) * 
x_1019::node<p_1018,left_24_944,right_24_945>@M * G(x_1019,left_24_944)&
left_24_944!=null & p_1018=parent_24_943 & right_24_945=null
   \/ (2;2;0) HP_946(parent_24_943,p_1018) * 
x_1019::node<p_1018,left_24_944,right_24_945>@M&p_1018=parent_24_943 & 
right_24_945=null & left_24_944=null
   \/ (1;0) HP_946(parent_24_943,p_1018) * HP_947(left_24_944,p_1018) * 
x_1019::node<p_1018,left_24_944,right_24_945>@M * G(x_1019,right_24_945)&
right_24_945!=null & p_1018=parent_24_943,
 H(p_1016,x_1017) ::=(1;2;0) x_1017::node<parent_24_943,left_24_944,right_24_945>@M * 
HP_946(parent_24_943,p_1016) * HP_947(left_24_944,p_1016)&right_24_945=null
   \/ (2;2;0) x_1017::node<parent_24_943,left_24_944,right_24_945>@M * 
HP_946(parent_24_943,p_1016)&right_24_945=null & left_24_944=null
   \/ (1;0) x_1017::node<parent_24_943,left_24_944,right_24_945>@M * 
HP_946(parent_24_943,p_1016) * HP_947(left_24_944,p_1016) * 
H(x_1017,right_24_945)&right_24_945!=null,
 HP_946(parent_24_943,p) ::= htrue,
 HP_947(left_24_1004,p_1005) |#| left_24_1004::node<x_990,left_24_944,right_24_945>@M ::=
  (1;2;0) left_24_1004::node<parent_24_943,left_24_944,right_24_945>@M * 
HP_947(left_24_944,x_990)&right_24_945=null
   \/ (2;2;0) emp&left_24_1004=null \/ (1;0) NONE]

*/
