data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
	or self::node<_, r> * r::cll<p, n-1> & self != p  
	inv n >= 0;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::cll<self, n-1>  
	inv n >= 0;

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node h)
  infer [H1,G1]
  requires H1(rest,h)
  ensures G1(rest,h);

{
	int n;
	
	if (rest == h)
		return 0; 
	else
	{
		n = count_rest(rest.next, h);
		n = n + 1;

		return n;
	}
}


/*

[ 

 H1(rest,h)&h!=rest --> rest::node<val_31_824,next_31_825>@M * 
  HP_8(next_31_825,h).

 HP_8(next_31_825,h)&h!=rest -->

 H1(next_31_825,h)&true.

 H1(rest,h)&h=rest --> G1(rest,h).

 rest::node<val_31_824,next_31_825>@M * G1(next_31_825,h) &
  h!=rest --> G1(rest,h).

]

*************************************
*******relational definition ********
*************************************
[ H1(rest_840,h_841) ::= rest_840::node<val_31_824,next_31_825>@M * (H1(next_31_825,h_841))&
h_841!=rest_840,
 G1(rest_844,h_845) ::= 
 emp&h_845=rest_844
 or rest_844::node<val_31_824,next_31_825>@M * (G1(next_31_825,h_845))&
    h_845!=rest_844
 ]

*/
