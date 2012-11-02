/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


ls<y> == self=y
  or self::node<_,q>*q::ls<y> & self!=y
inv true;

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


/*

ERROR : possible to fix bind translation
for pass-by-ref parameters?

{
boolean v_bool_38_552;
v_bool_38_552 = {
131::is_null___$node(x)
};
127::if (v_bool_38_552) [LABEL! 127,0: {
x = y
}]
else [LABEL! 127,1: {
{
node v_node_42_551;
v_node_42_551 = 129::bind x to (val_42_549,next_42_550) [read] in 
{next_42_550
};
128::append$node~node(v_node_42_551,y) rec
}
}]
*/
void append(ref node x, node y)
  requires x::ls<null>*y::ls<null> 
  ensures x'::ls<null>; //'
//requires x::ll<n> * y::ll<m>
//ensures x'::ll<n+m>; //'
{
    if (x==null) { 
        x = y;
    }
	else {
       append(x.next, y);
    }
}


void append3(ref node x, node y)
  requires x::ls<null>*y::ls<null> 
  ensures x'::ls<null>; //'
//requires x::ll<n> * y::ll<m>
//ensures x'::ll<n+m>; //'
{
    if (x==null) { 
        x = y;
    }
	else {
      bind x to (_,s) in {
       append3(s, y);
      }
    }
}
